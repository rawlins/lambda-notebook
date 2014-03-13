#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re
from numbers import Number
from lamb import utils, parsing
from lamb.utils import *
#import logic, utils

# constant for third truth value
Maybe = 2

class OntoSet(object):
    def __init__(self, finite, values):
        self.finite = finite
        self.values = values

    def check(self,x):
        if self.values.finite:
            return (x in self.values.values)
        else:
            return self.values.infcheck(x)

    def __contains__(self,x):
        return self.check(x)

    def infcheck(self,x):
        raise NotImplementedError("No type checker for abstract infinite set")

class SimpleInfiniteSet(OntoSet):
    """Contains all strings prefaced with one char prefix."""
    def __init__(self,prefix):
        OntoSet.__init__(self, 0, set())
        self.prefix = prefix[0]
        # TODO better error checking

    def infcheck(self,x):
        return (len(x) > 0 and x[0]==prefix)

class SimpleIntegerSet(OntoSet):
    """pretend infinite set for integers, does not implement full infinity"""
    def __init__(self):
        OntoSet.__init__(self, 0,set())

    def infcheck(self,x):
        return isinstance(x,int)

class AbstractType(object):
    def __init__(self):
        self.symbol = None

    def functional(self):
        raise NotImplementedError

    def check(self, x):
        raise NotImplementedError

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        raise NotImplementedError

    def __repr__(self):
        return re.sub(r'[\s]+', '', self.__str__())



class OntoType(AbstractType):
    """Class for atomic types.  The core atomic type interface:

    symbol: the name of the type.
    functional(): must return False.

    Extras:
    values: an object implementing the OntoSet interface representing the set that this type characterizes.
    """
    def __init__(self, symbol, values=None, name=None):
        self.symbol = symbol
        if name is None:
            self.name = symbol
        else:
            self.name = name
        if values is None:
            self.values = SimpleInfiniteSet("c" + symbol)
        else:
            self.values = values
        self.undetermined = False
        # pre-escape because of the use of "?" for undetermined type
        self.regex = re.compile(re.escape(self.symbol))

    def functional(self):
        return 0

    def check(self, x):
        return self.values.check(x)

    def __eq__(self, other):
        try:
            return self.symbol == other.symbol  # and self.values == other.values
        except AttributeError:
            return False

    def equal(self, other):
        if isinstance(other, UndeterminedType):
            return other.equal(self)
        elif other.undetermined:
            return Maybe
        else:
            return self.__eq__(other)

    def __hash__(self):
        return hash(self.symbol)

    def __str__(self):
        return "%s" % self.symbol

    def __repr__(self):
        return self.__str__()

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self):
        return ensuremath(self.__str__())

    def _repr_latex_(self):
        return self.latex_str()

    def add_internal_argument(self, arg_type):
        return FunType(arg_type, self)

    def unify(self, other, unify_control_fun):
        if self == other:
            return (self, other)
        else:
            return (None, None)

class FunType(AbstractType):
    """Class for non-atomic (functional) binary types.  These characterize a set of functions.
    The core functional type interface:

    functional(): must return True.
    left: the input/left type of functions in the set.
    right: the output/right type of functions in the set.
    """
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.undetermined = (left.undetermined or right.undetermined)

    def functional(self):
        return 1

    def check(self, x):
        raise NotImplementedError()

    def __str__(self):
        return "<%s,%s>" % (self.left, self.right)

    def __eq__(self, other):
        try:
             return other.left == self.left and other.right == self.right
        except AttributeError:
            return False

    def equal(self, other):
        #if self.undetermined or other.undetermined:
        #    return self.left.equal(other.left) and self.right.equal(other.right)
        #else:
        #    return self.__eq__(other)
        if not other.functional():
            if other.undetermined:
                return Maybe
            else:
                return False
        r1 = self.left.equal(other.left)
        r2 = self.right.equal(other.right)
        if r1 == False or r2 == False:
            return False
        elif r1 == Maybe or r2 == Maybe:
            return Maybe
        else:
            return True

    def __hash__(self):
        return hash(self.left) ^ hash(self.right)

    def __repr__(self):
        return re.sub(r'[\s]+', '', self.__str__())

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self):
        return ensuremath("\\langle{}%s,%s\\rangle{}" % (self.left.latex_str(), self.right.latex_str()))

    def _repr_latex_(self):
        return self.latex_str()

    def add_internal_argument(self, arg_type):
        return FunType(self.left, self.right.add_internal_argument(arg_type))

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "<")
        if next is None:
            return (None, i)
        else:
            i = next
            (left, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, ",", "Missing comma")
            (right, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, ">", "Unmatched <")
            return (FunType(left, right), i)

    @classmethod
    def local_unify(cls, a, b):
        if a.functional():
            if b.functional():
                if a.left.equal(b.left) == True and a.right.equal(b.right) == True:
                    return (a, b)
        return (None, None)

    def unify(self, other, unify_control_fun):
        if isinstance(other, FunType):
            s_left, o_left = unify_control_fun(self.left, other.left)
            s_right, o_right = unify_control_fun(self.right, other.right)
            if s_left is None or s_right is None:
                return (None, None)
            result_a = FunType(s_left, s_right)
            result_b = FunType(o_left, o_right)
            return (result_a, result_b)
        else:
            return (None, None)


class SetType(AbstractType):
    def __init__(self, ctype):
        self.content_type = ctype
        self.undetermined = False

    def function(self):
        return False

    def check(self, x):
        raise NotImplementedError()

    def __str__(self):
        return "{%s}" % str(self.content_type)

    def latex_str(self):
        return "\{%s\}" % self.content_type.latex_str()

    def __eq__(self, other):
        if isinstance(other, SetType):
            return self.content_type == other.content_type
        else:
            return False

    def __hash__(self):
        return hash("Set") ^ hash(self.content_type)

    def equal(self, other):
        # TODO: is this too rigid?
        if isinstance(other, SetType):
            return self.content_type.equal(other.content_type)
        else:
            return False

    def unify(self, other, unify_control_fun):
        if isinstance(other, SetType):
            result_s, result_o = unify_control_fun(self.content_type, other.content_type)
            if result_s is None:
                return (None, None)
            else:
                return (SetType(result_s), SetType(result_o))
        else:
            return (None, None)

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "{")
        if next is None:
            return (None, i)
        else:
            i = next
            (ctype, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, "}", "Unmatched {")
            return (SetType(ctype), i)

class TupleType(AbstractType):
    def __init__(self, *signature):
        self.signature = tuple(signature)
        self.undetermined = False

    def functional(self):
        return False

    def check(self, x):
        raise NotImplementedError()

    def __str__(self):
        return "(%s)" % ",".join([str(self.signature[i]) for i in range(len(self.signature))])

    def latex_str(self):
        return ensuremath("(%s)" % ", ".join([self.signature[i].latex_str() for i in range(len(self.signature))]))

    def __eq__(self, other):
        try:
            # just use tuple equality?
            for i in range(len(self.signature)):
                if not self.signature[i] == other.signature[i]:
                    return False
            return True
        except AttributeError:
            return False

    def equal(self, other):
        #if self.undetermined or other.undetermined:
        #    return self.left.equal(other.left) and self.right.equal(other.right)
        #else:
        #    return self.__eq__(other)
        try:
            othersig = other.signature
        except:
            if other.undetermined:
                return Maybe
            return False
        if len(self.signature) != len(othersig):
            return False
        results = set([self.signature[i].equal(othersig[i]) for i in range(len(self.signature))])
        if False in results:
            return False
        if Maybe in results:
            return Maybe
        return True

    def __hash__(self):
        return hash(self.signature)

    #def __repr__(self):
    #    return self.__str__()

    def __call__(self, other):
        return FunType(self, other)

    def __getitem__(self, i):
        return self.signature[i]

    def _repr_latex_(self):
        return self.latex_str()

    def unify(self, other, unify_control_fun):
        if isinstance(other, TupleType) and len(self.signature) == len(other.signature):
            l = [unify_control_fun(self.signature[i], other.signature[i]) for i in range(len(self.signature))]
            self_result = [x[0] for x in l]
            other_result = [x[1] for x in l]
            if None in (set(self_result)) or None in set(other_result):
                return (None, None)
            else:
                return (TupleType(*self_result), TupleType(*other_result))
        else:
            return (None, None)

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "(")
        if next is None:
            return (None, i)
        else:
            i = next
            signature = []
            (m, i) = parse_control_fun(s, i)
            signature.append(m)
            i = parsing.consume_char(s, i, ",", "Missing comma in tuple (no 1-tuples allowed)")
            (m, i) = parse_control_fun(s, i)
            signature.append(m)
            while i < len(s) and s[i] == ",":
                i = parsing.consume_char(s, i, ",", "Missing comma in tuple (no 1-tuples allowed)")
                (m, i) = parse_control_fun(s, i)
                signature.append(m)
            i = parsing.consume_char(s, i, ")", "Unmatched ( in tuple type")
            return (TupleType(*signature), i)       

    #def add_internal_argument(self, arg_type):
    #    return FunType(self.left, self.right.add_internal_argument(arg_type))


# TODO make real singleton
class UndeterminedType(OntoType):
    """Class for a singleton placeholder type."""
    def __init__(self, contained=None):
        super().__init__(symbol="?", values=set(), name="undetermined-type")
        self.undetermined = True
        c = contained
        while isinstance(c, UndeterminedType):
            c = c.contained
        if c is None:
            self.left = self
            self.right = self
        elif c.functional():
            self.left = c.left
            self.right = c.right
        else:
            pass # leave left and right unset...TODO is this right?
        self.contained = c

    #Note: __eq__ is still inherited from OntoType, and differs from 'equal'.

    def functional(self):
        if self.contained is None:
            return False # TODO is this right?
        else:
            return self.contained.functional()

    def __hash__(self):
        if self.contained is None:
            return hash(self.symbol)
        else:
            return hash(self.contained) ^ hash(self.symbol)

    def __eq__(self, other):
        """This implements strict equality.  Two undetermined types are equal only if they contain the same type (or both contain None).
        An undetermined type is not equal to a regular type.
        """
        if isinstance(other, UndeterminedType):
            if self.contained is None and other.contained is None:
                return True
            else:
                return self.contained == other.contained
        else:
            return False

    # @property
    # def symbol(self):
    #     if self.contained is None:
    #         return "?"
    #     elif isinstance(self.contained, OntoType):
    #         return self.contained.symbol + "?"
    #     elif isinstance(self.contained, FunType):
    #         # not sure about this...
    #         return str(self.contained) + "?"
    #     else:
    #         raise NotImplementedError

    def equal(self, other):
        """This implements trivalent equality.  In this case, is guaranteed to return either Maybe or False."""
        # Note that this _must never_ call any of the basic class' __eq__ function with this object, 
        #  or infinite recursion will result.  (TODO: better way around this?)
        if self.contained is None:
            return Maybe
        else:
            result = self.contained.equal(other)
            # downgrade a true result to a maybe
            if result == True or result == Maybe:
                return Maybe
            else:
                return False

    @classmethod
    def fun_arg_ok(cls, fun, arg):
        if fun.type.functional():
            return flexible_equal(fun.type.left, arg.type)
            # TODO: this logic is not fully general -- doesn't cover embedded undetermined types in arg or fun.left
            #if isinstance(arg.type, UndeterminedType) or isinstance(fun.type.left, UndeterminedType) or fun.type.left == arg.type:
            #    return True
            #else:
            #    return False
        elif isinstance(fun.type, UndeterminedType):
            return True
        else:
            return False

    def latex_str(self):
        if self.contained is None:
            return OntoType.latex_str(self)
        else:
            c_str = self.contained.latex_str()
            return ensuremath(c_str + "_{?}")

    def __str__(self):
        if self.contained is None:
            return OntoType.__str__(self)
        else:
            c_str = str(self.contained)
            return "?" + c_str

    def unify(self, other, unify_control_fun):
        if self.contained is None:
            return (UndeterminedType(other), other)
        else:
            if isinstance(other, UndeterminedType):
                # probably inefficient but simplifying recursion -- switch perspective to the other
                (r_b, r_a) = other.unify(self.contained, unify_control_fun)
                # switch the order back
                if r_a is not None:
                    # weak unification: flag with uncertainty
                    r_a = UndeterminedType(r_a)
                return (r_a, r_b)
            else:
                (r_a, r_b) = unify_control_fun(self.contained, other)
                if r_a is not None:
                    r_a = UndeterminedType(r_a)
                return (r_a, r_b)


    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "?")
        if next is None:
            return (None, i)
        try:
            result, next = parse_control_fun(s, next)
        except:
            result = None
        if result is None:
            # TODO, double check that this is sufficiently general...
            # basically, aggressively consume a ? if can't find a type right after it
            #return (UndeterminedType(), i+1)
            return (None, i)
        else:
            return (UndeterminedType(result), next)


# used while parsing to defer type evaluation
undetermined_type = UndeterminedType()

def determine_type(t):
    if isinstance(t, UndeterminedType):
        if t == undetermined_type:
            return t
        else:
            return t.contained
    else:
        return t


class TypeConstraints(set):
    def __init__(self, *init):
        set.__init__(self, *init)

    def check(self, typed_object):
        for c in self:
            r = c.equal(typed_object)
            if r == False:
                return False
            # Maybe or True: we are ok.
        return True

    def consistent(self):
        if len(self) > 1:
            raise NotImplementedError  #TODO: implement consistency checking
        else:
            return True

    def most_certain_type(self):
        if len(self) > 1:
            raise NotImplementedError # TODO: implement >1 constraint
        elif len(self) == 1:
            return next(iter(self))
        else:
            # no constraints: completely undetermined type
            return undetermined_type




def flexible_equal(t1, t2):
    result = t1.equal(t2)
    if result == Maybe or result == True:
        return True
    else:
        return False


# TODO: finish implementing this...hard
class VariableType(OntoType):
    def __init__(self, symbol):
        self.symbol = symbol
        self.name = "variable-type"
        self.values = set()
        self.left = self
        self.right = self

    def type_compare(self, other, assignment=None):
        pass


class TypeMismatch(Exception):
    def __init__(self, i1, i2, mode=None):
        #print("type mismatch '%s', '%s'" % (fun, arg))
        self.i1 = i1
        self.i2 = i2
        try:
            self.type1 = self.i1.type
        except AttributeError:
            self.type1 = undetermined_type
        try:
            self.type2 = self.i2.type
        except AttributeError:
            self.type2 = undetermined_type
        if mode is None:
            self.mode = "unknown"
        else:
            self.mode = mode

    def item_str(self, i, t, latex=False):
        if i is None:
            return None
        if isinstance(i, AbstractType):
            if latex:
                return "type %s" % i.latex_str()
            else:
                return "type %s" % repr(i)
        elif isinstance(i, str):
            if t is None or t is undetermined_type:
                return "'" + i + "'"
            else:
                if latex:
                    return "'%s'/%s" % (i, t.latex_str())
                else:
                    return "'%s'/%s" % (i, repr(t))
        else:
            if t is None or t is undetermined_type:
                if latex:
                    return "'" + i.latex_str() + "'"
                else:
                    return "'" + repr(i) + "'"
            else:
                if latex:
                    return "'%s'/%s" % (i.latex_str(), t.latex_str())
                else:
                    return "'%s'/%s" % (repr(i), repr(t))

    def __str__(self):
        return self.description(latex=False)

    def latex_str(self):
        return self.description(latex=True)

    def description(self, latex=False):
        is_1 = self.item_str(self.i1, self.type1, latex=latex)
        is_2 = self.item_str(self.i2, self.type2, latex=latex)
        if is_1 is None:
            if is_2 is None:
                return "Type mismatch, unknown context (mode: %s)" % self.mode
            else:
                return "Type mismatch on %s (mode: %s)" % (is_2, self.mode)
        else:
            if is_2 is None:
                return "Type mismatch on %s (mode: %s)" % (is_1, self.mode)
            else:
                return "Type mismatch: %s and %s conflict (mode: %s)" % (is_1, is_2, self.mode)


    # def latex_str(self):
    #     return "Type mismatch: %s and %s conflict (mode: %s)" % (self.item_str(self.i1, self.type1, True), self.item_str(self.i2, self.type2, True), self.mode)

    def _repr_latex_(self):
        return self.latex_str()

    def __repr__(self):
        return self.__str__()



class TypeSystem(object):
    """Parent class for a type system.  A TypeSystem provides:
     * unification functions for variables and function application
     * an identity criteria
     * some FA checking utilities
    """
    def __init__(self, name=None, atomics=None, nonatomics=None):
        self.name = name
        if self.name is None:
            self.raisemsg = "function-argument combination"
        else:
            self.raisemsg = name +  " function-argument combination"
        self._parse_cache = dict()
        self.atomics = set()
        if atomics is not None:
            for a in atomics:
                self.add_atomic(a)
        self.nonatomics = set()
        if nonatomics is not None:
            for a in nonatomics:
                self.add_nonatomic(a)

    def add_atomic(self, atomic):
        self._parse_cache[atomic.regex] = atomic
        self.atomics.add(atomic)

    def remove_atomic(self, atomic):
        if atomic in self.atomics:
            self.atomics.remove(atomic)
            del self._parse_cache[atomic]

    def add_nonatomic(self, na):
        self.nonatomics.add(na)

    def remove_nonatomic(self, na):
        self.nonatomics.remove(na)

    def atomic_parser(self, s, i):
        # note: no checking for multiple matches...
        for r in self._parse_cache.keys():
            (m_group, new_i) = parsing.consume_pattern(s, i, r)
            if m_group is None:
                continue
            return (self._parse_cache[r], new_i)
        raise TypeParseError("Unknown atomic type", s, i)
        #return (None, None)

    def type_parser_recursive(self, s, i=0):
        for na in self.nonatomics:
            result, next = na.parse(s, i, self.type_parser_recursive)
            if result is not None:
                # one of the non-atomics succeeded
                return (result, next)
        # none of the non-atomics succeeded, so try atomic parser.
        if i >= len(s):
            raise TypeParseError("Missing type", s, i)
        (result, i) = self.atomic_parser(s, i)
        # may return None?
        return (result, i)

    def type_parser(self, s):
        (r, i) = self.type_parser_recursive(s)
        return r

    def fun_arg_check_bool_old(self, fun, arg):
        return (fun.type.functional() and 
                self.type_allowed(fun.type) and
                self.type_allowed(arg.type) and
                fun.type.left == arg.type)

    def fun_arg_check_bool(self, fun, arg):
        return (fun.type.functional() and
                self.type_allowed(fun.type) and
                self.type_allowed(arg.type) and
                self.eq_check(fun.type.left, arg.type))

    def local_unify_old(self, a, b):
        """Unify two types via some scheme.  
        If a and b are compatible, return (possibly changed) versions of a and b as a tuple.
        If a and b are incompatible, return (None, None).
        The default implementation simply checks strict equality.
        """
        if a == b:
            # TODO: should check whether type is allowed here?
            return (a,b)
        else:
            return (None, None)

    def unify_old(self, a, b):
        if a.functional():
            if b.functional():
                left_a, left_b = self.unify(a.left, b.left)
                right_a, right_b = self.unify(a.right, b.right)
                if left_a is None or right_a is None:
                    return (None, None)
                result_a = FunType(left_a, right_a)
                result_b = FunType(left_b, right_b)
                return (result_a, result_b)
        # at least one of the two is not functional
        # this will handle undetermined_type appropriately
        return self.local_unify(a, b)

    def local_unify(self, a, b):
        return self.unify(a,b)

    def check_type(self, t):
        return (t in self.atomics or t.__class__ in self.nonatomics)

    def unify(self, a, b):
        if not (self.check_type(a) and self.check_type(b)):
            return (None, None)
        (attempt1_a, attempt1_b) = a.unify(b, self.unify)
        # try in the other order, reverse results
        (attempt2_b, attempt2_a) = b.unify(a, self.unify)
        if attempt1_a is None:
            if attempt2_a is None:
                return (None, None)
            else:
                return (attempt2_a, attempt2_b)
        else:
            if attempt2_a is None:
                return (attempt1_a, attempt1_b)
            else:
                # TODO: both attempts succeeded, what to do??
                if attempt1_a == attempt2_a and attempt1_b == attempt2_b:
                    return (attempt1_a, attempt1_b)
                else:
                    raise ValueError("Does this get raised??")

    def local_unify_fa(self, fun, arg):
        return self.unify_fa(fun, arg)

    def unify_fa(self, fun, arg):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's type, the argument's type, and the output type.
        If this fails, returns (None, None, None).
        The default implementation tries unification with local_unify and reports the result."""
        #r = self.fun_arg_check_bool(fun, arg)
        # TODO: this doesn't handle undetermined function types....
        if fun.functional():
            a,b = self.unify(fun.left, arg)
            if a is None:
                return (None, None, None)
            else:
                return (FunType(a, fun.right), b, fun.right)
        else:
            return (None, None, None)

    def fun_arg_check(self, fun, arg):
        if not self.fun_arg_check_bool(fun, arg):
            raise TypeMismatch(fun.type, arg.type, "function-argument combination")

    def eq_check(self, a, b):
        #return (a == b)
        r_a, r_b = self.unify(a,b)
        return (r_a is not None)

    def type_allowed(self, a):
         return True

    # def try_parse_type(self, s, onto=None):
    #     """Attempt to get a type name out of s.

    #     Assumes s is already stripped."""
    #     # TODO: generalize to arbitrary types!
    #     # deal with basic types first
    #     if s == "e":
    #         return type_e
    #     elif s == "t":
    #         return type_t
    #     elif s == "n":
    #         return type_n
    #     elif onto is not None and s in onto:
    #         return onto[s]
    #     # TODO: proper handling of unrecognized atomic type
    #     raise NotImplementedError("not implemented: non-atomic type parsing")

    def latex_str(self):
        return "Type system with atomic types: " + ensuremath(", ".join([a.latex_str() for a in self.atomics]))


    def _repr_latex_(self):
        return self.latex_str()


class StrictTypeSystem(TypeSystem):
    def __init__(self, atomics, nonatomics):
        super().__init__("strict", atomics=atomics, nonatomics=nonatomics)

    def type_allowed(self, a):
        # TODO: add the recursion here so that this works.  
        # However, I'm not sure why I'd use this class (maybe for teaching?) so I kind of stopped working on it.
        raise NotImplementedError
        return a in self.atomics

    def fun_arg_check_bool(self, fun, arg):
        return (fun.type.functional() and 
                self.type_allowed(fun.type) and
                self.type_allowed(arg.type) and
                fun.type.left == arg.type)

    def fun_arg_check(self, fun, arg):
        if not self.type_allowed(fun.type):
            raise TypeMismatch(fun.type, None, "Type disallowed")
        if not self.fun_arg_check_bool(fun, arg):
            raise TypeMismatch(fun.type, arg.type, self.raisemsg)

class SimpleUnderTypeSystem(TypeSystem):
    """This type system allows a type to be completely undetermined, or one of the regular atomic types"""
    def __init__(self, atomics=None, nonatomics=None):
        super().__init__(name="simple undetermined", atomics=atomics, nonatomics=nonatomics)
        self.add_atomic(undetermined_type)

    def fun_arg_check_bool(self, fun, arg):
        # this was the first logic for undetermined types that I tries: no inference really.
        return fun.type == undetermined_type or arg.type == undetermined_type or super().fun_arg_check_bool(fun, arg)

    def local_unify(self, a, b):
        r = a.equal(b)
        if r == True:
            return (a, b)
        elif r == False:
            return (None, None)
        else: #Maybe
            if a == undetermined_type:
                if b == undetermined_type:
                    return (a, b)
                else:
                    return (undetermined_type, b)
            else:
                if b == undetermined_type:
                    return (a, undetermined_type)
                else:
                    return (a,b)

    def eq_check(self, a, b):
        return flexible_equal(a,b)

class UnderTypeSystem(TypeSystem):
    """Allows for rich undetermined types. TODO: expand"""
    def __init__(self, atomics=None, nonatomics=None):
        super().__init__("undetermined", atomics=atomics, nonatomics=nonatomics)
        self.add_atomic(undetermined_type)
        self.add_nonatomic(UndeterminedType)

    def fun_arg_check_bool(self, fun, arg):
        if fun.type.functional():
            return flexible_equal(fun.type.left, arg.type)
            # TODO: this logic is not fully general -- doesn't cover embedded undetermined types in arg or fun.left
            #if isinstance(arg.type, UndeterminedType) or isinstance(fun.type.left, UndeterminedType) or fun.type.left == arg.type:
            #    return True
            #else:
            #    return False
        elif isinstance(fun.type, UndeterminedType):
            return True
        else:
            return False


    # a, a   -> a, a
    # a, ?a  -> a, a
    # a, ?   -> a, a
    # ?a, a  -> a, a
    # ?a, ?a -> a, a
    # ?a, ?  -> a, a
    # ?, a   -> a, a
    # ?, ?a  -> a, a
    # ?, ?   -> ?, ?
    def local_unify_strong(self, a, b):
        r = a.equal(b)
        if r == True:
            return (a, b)
        elif r == False:
            return (None, None)
        else: #Maybe
            if a == undetermined_type:
                if b == undetermined_type:
                    return (a, b)
                else:
                    d = determine_type(b)
                    return (d, d)
            else:
                d = determine_type(a)
                return (a,a)

    # a, a   -> a, a
    # a, ?a  -> a, ?a
    # a, ?   -> a, ?a
    # ?a, a  -> ?a, a
    # ?a, ?a -> ?a, ?a
    # ?a, ?  -> ?a, ?a
    # ?, a   -> ?a, a
    # ?, ?a  -> ?a, ?a
    # ?, ?   -> ?, ?
    def local_unify_weak(self, a, b):
        r = a.equal(b)
        if r == True:
            return (a, b)
        elif r == False:
            return (None, None)
        else: #Maybe
            if a == undetermined_type:
                if b == undetermined_type:
                    return (a, b)
                else:
                    return (UndeterminedType(b), b)
            else:
                if b == undetermined_type:
                    return (a, UndeterminedType(a))
                else:
                    return (a,b)

    def local_unify_old(self, a, b):
        return self.local_unify_weak(a,b)

    def unify_old(self, a, b):
        if a.functional():
            if b.functional():
                left_a, left_b = self.unify(a.left, b.left)
                right_a, right_b = self.unify(a.right, b.right)
                if left_a is None or right_a is None:
                    return (None, None)
                result_a = FunType(left_a, right_a)
                result_b = FunType(left_b, right_b)
                if left_a.undetermined or right_a.undetermined:
                    result_a = UndeterminedType(result_a)
                if left_b.undetermined or right_b.undetermined:
                    result_b = UndeterminedType(result_b)
                return (result_a, result_b)
        # at least one of the two is not functional
        # this will handle undetermined_type appropriately
        return self.local_unify(a, b)





    # implements the following scheme for resolving uncertainty:
    # <?,y>,  ?  -> <?,y>, ?, y
    # <?x,y>, ?  -> <x,y>, x, y
    # <x,y>,  ?  -> <x,y>, x, y
    # <?,y>,  ?x -> <x,y>, x, y
    # <?x,y>, ?x -> <x,y>, x, y
    # <x,y>,  ?x -> <x,y>, x, y
    # <?,y>,  x  -> <x,y>, x, y
    # <?x,y>, x  -> <x,y>, x, y
    # <x,y>,  x  -> <x,y>, x, y
    # ?, ?       -> <?,?>, ?, ?
    # ?, ?x      -> <x,?>, x, ?
    # ?, x       -> <x,?>, x, ?
    # always collapse recursive uncertainty
    def local_unify_fa_strong(self, fun, arg):
        if fun.functional():
            new_f_left, new_a = self.local_unify_strong(fun.left, arg)
            if new_f_left is None:
                return (None, None, None)
            new_out = fun.right
            new_f = FunType(new_f_left, new_out)
            return (new_f, new_a, new_out)
        elif fun == undetermined_type:
            new_a = determine_type(arg)
            new_f = FunType(new_a, undetermined_type)
            return (new_f, new_a, undetermined_type)
        else:
            return (None, None, None)


    # implements the following scheme for resolving uncertainty:
    # <?,y>,  ?  -> <?,y>, ?, ?y
    # <?x,y>, ?  -> <?x,y>, ?x, ?y
    # <x,y>,  ?  -> <x,y>, ?x, ?y
    # <?,y>,  ?x -> <?x,y>, ?x, ?y
    # <?x,y>, ?x -> <?x,y>, ?x, ?y
    # <x,y>,  ?x -> <x,y>, ?x, ?y
    # <?,y>,  x  -> <?x,y>, x, ?y
    # <?x,y>, x  -> <?x,y>, x, ?y
    # <x,y>,  x  -> <x,y>, x, y
    # ?, ?       -> ?<?,?>, ?, ?
    # ?, ?x      -> ?<?x,?>, ?x, ?
    # ?, x       -> ?<x,?>, x, ?
    # always preserve recursive uncertainty (TODO: what is best in practice?)
    # output is uncertain if there is uncertainty in x, y, or the function's type.
    def local_unify_fa_weak(self, fun, arg):
        if fun.functional():
            new_f_left, new_a = self.local_unify_weak(fun.left, arg)
            if new_f_left is None:
                return (None, None, None)
            if (isinstance(fun, UndeterminedType) or 
                        isinstance(fun.left, UndeterminedType) or
                        isinstance(fun.right, UndeterminedType) or
                        isinstance(arg, UndeterminedType)):
                new_out = UndeterminedType(fun.right)
            else:
                new_out = fun.right
            new_f = FunType(new_f_left, fun.right)
            if isinstance(fun, UndeterminedType):
                new_f = UndeterminedType(new_f)
        elif fun == undetermined_type:
            new_a = arg
            new_f = UndeterminedType(FunType(new_a, undetermined_type))
            new_out = undetermined_type
        else:
            return (None, None, None)
        return (new_f, new_a, new_out)

    def local_unify_fa(self, f, a):
        return self.local_unify_fa_weak(f,a)

    def unify_fa_weak(self, fun, arg):
        """The main distinguishing property of this is that the type of the whole inherits some
        uncertainty from any uncertain parts."""
        if fun.functional():
            new_f_left, new_a = self.unify(fun.left, arg)
            if new_f_left is None:
                return (None, None, None)
            if (isinstance(fun, UndeterminedType) or 
                        isinstance(fun.left, UndeterminedType) or
                        isinstance(fun.right, UndeterminedType) or
                        isinstance(arg, UndeterminedType)):
                new_out = UndeterminedType(fun.right)
            else:
                new_out = fun.right
            new_f = FunType(new_f_left, fun.right)
            if isinstance(fun, UndeterminedType):
                new_f = UndeterminedType(new_f)
        elif fun == undetermined_type:
            new_a = arg
            new_f = UndeterminedType(FunType(new_a, undetermined_type))
            new_out = undetermined_type
        else:
            return (None, None, None)
        return (new_f, new_a, new_out)

    def unify_fa(self, f, a):
        return self.unify_fa_weak(f, a)

    def eq_check(self, a, b):
        return flexible_equal(a,b)

class TypeParseError(Exception):
    def __init__(self, msg, s, i):
        self.s = s
        self.i = i
        self.msg = msg

    def __str__(self):
        if self.s == None or self.i == None:
            return msg
        if self.i >= len(self.s):
            return "%s at point '%s!here!" % (self.msg, self.s)
        else:
            return "%s at point '%s!here!%s'" % (self.msg, self.s[0:self.i], self.s[self.i:])

def consume_char(s, i, match, error=None):
    if i >= len(s):
        if error is not None:
            raise TypeParseError(error, s, i)
        else:
            return None
    if s[i] == match:
        return i + 1
    else:
        if error is None:
            return None
        else:
            raise TypeParseError(error, s, i)

def consume_pattern(s, i, regex, error=None):
    if i > len(s):
        if error is not None:
            raise TypeParseError(error, s, i)
        else:
            return (None, None)
    m = regex.match(s[i:])
    if m:
        return (m.group(), m.end() + i)
    else:
        if error is None:
            return (None, None)
        else:
            raise TypeParseError(error, s, i)


def consume_atomic_type(s, i):
    # TODO: generalize
    if s[i] == "e":
        return (type_e, i+1)
    elif s[i] == "t":
        return (type_t, i+1)
    elif s[i] == "n":
        return (type_n, i+1)
    else:
        raise TypeParseError("Unknown atomic type", s, i)


def type_parser_recursive(s, i=0):
    next = consume_char(s, i, "<")
    if next is None:
        (result, i) = consume_atomic_type(s, i)
        return (result, i)
    else:
        i = next
        (left, i) = type_parser_recursive(s, i)
        i = consume_char(s, i, ",", "Missing comma")
        (right, i) = type_parser_recursive(s, i)
        i = consume_char(s, i, ">", "Unmatched <")
        return (FunType(left, right), i)

def type_parser(s):
    (r, i) = type_parser_recursive(s)
    return r

def setup_type_constants():
    global type_e, type_t, type_n, type_property, type_transitive, basic_system, under_system

    type_e = OntoType("e", SimpleInfiniteSet("c"))
    type_t = OntoType("t", OntoSet(0,[0,1]))
    type_n = OntoType("n", SimpleIntegerSet())
    type_property = FunType(type_e, type_t)
    type_transitive = FunType(type_e, type_property)
    basic_system = TypeSystem(atomics={type_e, type_t, type_n}, nonatomics={FunType, TupleType})
    under_system = UnderTypeSystem(atomics={type_e, type_t, type_n, undetermined_type}, nonatomics={FunType, TupleType, UndeterminedType, SetType})

setup_type_constants()


