#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re, random
from numbers import Number
from lamb import utils, parsing
from lamb.utils import *
#import logic, utils

# constant for third truth value
global Maybe, random_len_cap
Maybe = 2

random_len_cap = 5


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

class TypeConstructor(object):
    def __init__(self):
        self.symbol = None

    def __len__(self):
        return 0

    def __getitem__(self, i):
        raise IndexError

    def __iter__(self):
        return iter(list())

    def functional(self):
        raise NotImplementedError

    def check(self, x):
        raise NotImplementedError

    def copy_local(self, *parts):
        """Return a copy of the type with any local properties preserved, but *parts substituted appropriately.

        Note that for complex types, this acts much like a factory function."""
        raise NotImplementedError

    def copy(self):
        return self.copy_local(*list(iter(self)))

    def __repr__(self):
        return re.sub(r'[\s]+', '', self.__str__())

    def __str__(self):
        raise NotImplementedError

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        raise NotImplementedError

    @classmethod
    def random(cls, random_ctrl_fun):
        raise NotImplementedError

    def bound_type_vars(self):
        """Finds any type variables in the type that are bound.  Reminder: in Hindley-Milner, the way it is normally used, all type variables are bound.
        So in practice, this finds all type variables."""
        accum = set()
        for part in iter(self):
            accum = accum | part.bound_type_vars()
        return accum

    def sub_type_vars(self, assignment):
        """Substitute type variables in `self` given the mapping in `assignment`.

        This does only one-place substitutions, so it won't follow chains if there are any."""
        l = list()
        dirty = False
        for i in range(len(self)):
            l.append(self[i].sub_type_vars(assignment))
            if l[i] is not self[i]:
                dirty = True
        if dirty:
            return self.copy_local(*l)
        else:
            return self

    def unify(self, other, unify_control_fun, data):
        """General function for type unification.  Not intended to be called directly.  See `TypeSystem.unify`."""
        if not isinstance(self, other.__class__):
            return (None, None)
        if len(self) != len(other):
            return (None, None)
        sig = list()
        for i in range(len(self)):
            (part_result, data) = unify_control_fun(self[i], other[i], data)
            if part_result is None:
                return (None, None)
            sig.append(part_result)
        return (self.copy_local(*sig), data)


class BasicType(TypeConstructor):
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
        # pre-escape because of the use of "?" for undetermined type
        self.regex = re.compile(re.escape(self.symbol))

    def functional(self):
        return False

    def check(self, x):
        return self.values.check(x)

    def __eq__(self, other):
        try:
            return self.symbol == other.symbol  # and self.values == other.values
        except AttributeError:
            return False

    def copy_local(self):
        return BasicType(self.symbol, self.values, self.name)

    def equal(self, other):
        raise NotImplementedError
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

    def unify(self, other, unify_control_fun, data):
        if self == other:
            return (self, data)
        else:
            return (None, None)




class FunType(TypeConstructor):
    """Class for non-atomic (functional) binary types.  These characterize a set of functions.
    The core functional type interface:

    functional(): must return True.
    left: the input/left type of functions in the set.
    right: the output/right type of functions in the set.
    """
    def __init__(self, left, right):
        self.left = left
        self.right = right
        TypeConstructor.__init__(self)

    def __len__(self):
        return 2

    def __getitem__(self, i):
        return (self.left, self.right)[i]

    def __iter__(self):
        return iter((self.left, self.right))

    def functional(self):
        return True

    def copy_local(self, l, r):
        return FunType(l, r)

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
        raise NotImplementedError
        if not other.functional():
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

    # def sub_type_vars(self, assignment):
    #     left_sub = self.left.sub_type_vars(assignment)
    #     right_sub = self.right.sub_type_vars(assignment)
    #     if left_sub is not self.left or right_sub is not self.right:
    #         return types.FunType(left_sub, right_sub)
    #     else:
    #         return self

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

    # @classmethod
    # def local_unify(cls, a, b):
    #     if a.functional():
    #         if b.functional():
    #             if a.left.equal(b.left) == True and a.right.equal(b.right) == True:
    #                 return (a, b)
    #     return (None, None)

    # def unify(self, other, unify_control_fun):
    #     if isinstance(other, FunType):
    #         s_left, o_left = unify_control_fun(self.left, other.left)
    #         s_right, o_right = unify_control_fun(self.right, other.right)
    #         if s_left is None or s_right is None:
    #             return (None, None)
    #         result_a = FunType(s_left, s_right)
    #         result_b = FunType(o_left, o_right)
    #         return (result_a, result_b)
    #     else:
    #         return (None, None)

    @classmethod
    def random(cls, random_ctrl_fun):
        return FunType(random_ctrl_fun(), random_ctrl_fun())



class SetType(TypeConstructor):
    """Type for sets.  See `lang.ConditionSet` and `lang.ListedSet`."""
    def __init__(self, ctype):
        self.content_type = ctype
        TypeConstructor.__init__(self)

    def __len__(self):
        return 1

    def __getitem__(self, i):
        return (self.content_type,)[i]

    def __iter__(self):
        return iter((self.content_type,))

    def copy_local(self, ctype):
        return SetType(ctype)

    def functional(self):
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
        raise NotImplementedError
        # TODO: is this too rigid?
        if isinstance(other, SetType):
            return self.content_type.equal(other.content_type)
        else:
            return False

    # def unify(self, other, unify_control_fun):
    #     if isinstance(other, SetType):
    #         result_s, result_o = unify_control_fun(self.content_type, other.content_type)
    #         if result_s is None:
    #             return (None, None)
    #         else:
    #             return (SetType(result_s), SetType(result_o))
    #     else:
    #         return (None, None)

    # def sub_type_vars(self, assignment):
    #     sub = self.content_type.sub_type_vars(assignment)
    #     if sub is not self.content_type:
    #         return SetType(sub)
    #     else:
    #         return self


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

    @classmethod
    def random(cls, random_ctrl_fun):
        return SetType(random_ctrl_fun())


class TupleType(TypeConstructor):
    """Type for tuples.  See `lang.Tuple`."""
    def __init__(self, *signature):
        if len(signature) == 0:
            raise ValueError("Tuple type can't be 0 length")
        self.signature = tuple(signature)
        TypeConstructor.__init__(self)

    def copy_local(self, *sig):
        return TupleType(*sig)

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
            if len(self.signature) != len(other.signature):
                return False
            # just use tuple equality?
            for i in range(len(self.signature)):
                if not self.signature[i] == other.signature[i]:
                    return False
            return True
        except AttributeError:
            return False

    def __len__(self):
        return len(self.signature)

    def __getitem__(self, i):
        return self.signature[i]

    def __iter__(self):
        return iter(self.signature)


    def equal(self, other):
        raise NotImplementedError
        try:
            othersig = other.signature
        except:
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

    def _repr_latex_(self):
        return self.latex_str()

    # def unify(self, other, unify_control_fun):
    #     if isinstance(other, TupleType) and len(self.signature) == len(other.signature):
    #         l = [unify_control_fun(self.signature[i], other.signature[i]) for i in range(len(self.signature))]
    #         self_result = [x[0] for x in l]
    #         other_result = [x[1] for x in l]
    #         if None in (set(self_result)) or None in set(other_result):
    #             return (None, None)
    #         else:
    #             return (TupleType(*self_result), TupleType(*other_result))
    #     else:
    #         return (None, None)

    # def sub_type_vars(self, assignment):
    #     l = list()
    #     dirty = False
    #     for i in range(len(self)):
    #         l.append(self.signature[i].sub_type_vars(assignment))
    #         if l[i] is not self.signature[i]:
    #             dirty = True
    #     if dirty:
    #         return TupleType(*l)
    #     else:
    #         return self

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
    @classmethod
    def random(cls, random_ctrl_fun):
        tuple_len = random.randint(2, random_len_cap)
        args = tuple([random_ctrl_fun() for i in range(0,tuple_len)])
        return TupleType(*args)

vartype_regex_str = r"[XYZ]'*"
vartype_regex = re.compile(vartype_regex_str)
vartype_regex_full = re.compile( "^" + vartype_regex_str + "$")

def is_vartype_symbol(x):
    m = vartype_regex_full.match(x)
    if m:
        return True
    else:
        return False


class VariableType(TypeConstructor):
    def __init__(self, symbol, number=None):
        if number:
            self.symbol = symbol[0] + "'" * number
            self.number = number
        else:
            self.symbol = symbol
            self.number = len(self.symbol[1:])
        self.name = symbol
        self.values = set()
        self.left = self # ???
        self.right = self # ???

    def functional(self):
        return True # ???

    def copy_local(self):
        return VariableType(self.symbol, self.number)
    
    def equal(self, other):
        raise NotImplementedError
        return Maybe
    
    def unify(self, t2, unify_control_fun, assignment):
        if self == t2:
            # does this really come up?
            return (self, assignment)
        if self in assignment:
            # need to check if existing assignment for t2 is compatible
            v_trans = self
            # follow any transitive sequences to the principle type
            while v_trans in assignment:
                (r_result, r_assign) = unify_control_fun(assignment[v_trans], t2, assignment)
                #print(v_trans, assignment[v_trans], (r_result, r_assign))
                if r_result is None:
                    return (None, None)
                v_trans = assignment[v_trans]
            # r_result is the (new) principle type
            # r_assign[v] = r_result
            v_trans = self
            # short-circuit any transitive pairs that led to r_result
            while v_trans in assignment:
                next_v = assignment[v_trans]
                assignment[v_trans] = r_result
                v_trans = next_v
            if isinstance(t2, VariableType):
                # ensure that t2's value gets back-converted to the discovered principle type, if relevant
                r_result, r_assign = t2.unify(r_result, unify_control_fun, r_assign)
                if r_result is None:
                    return (None, None)
            return r_result, r_assign
        else:
            # t2 is guaranteed to be the principle type
            # note that if t2 is a var, this always uses the second var as the principle.
            # requires full alpha conversion before unification.
            assignment[self] = t2
            r_result = t2
            return (r_result, assignment)
        
    
    def bound_type_vars(self):
        return set((self,))
    
    def sub_type_vars(self, assignment, trans_closure=False):
        if self in assignment:
            x = assignment[self]
            if trans_closure:
                while x in assignment:
                    x = assignment[x] # TODO, should make this loop safe (relies on there never being loops in the assignment)
            return x
        else:
            return self

    def __hash__(self):
        return hash(self.symbol)

    def __eq__(self, other):
        """This implements token equality.  This is _not_ semantic equality due to type variable binding.
        """
        if isinstance(other, VariableType):
            return self.symbol == other.symbol
        else:
            return False
        
    def __str__(self):
        return self.symbol
    
    def latex_str(self):
        return utils.ensuremath(self.__str__())
    
    def _repr_latex_(self):
        return self.latex_str()
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        (m_group, new_i) = parsing.consume_pattern(s, i, vartype_regex)
        if m_group is None:
            return (None, i)
        else:
            return (VariableType(m_group), new_i)

    @classmethod
    def random(cls, random_ctrl_fun):
        primes = random.randint(0, 10)
        var = random.choice(("X", "Y", "Z"))
        return VariableType(var, number=primes)



def flexible_equal(t1, t2):
    result = t1.equal(t2)
    if result == Maybe or result == True:
        return True
    else:
        return False



class TypeMismatch(Exception):
    """Exception for type mismatches of all sorts."""
    def __init__(self, i1, i2, mode=None):
        #print("type mismatch '%s', '%s'" % (fun, arg))
        self.i1 = i1
        self.i2 = i2
        try:
            self.type1 = self.i1.type
        except AttributeError:
            self.type1 = "?"
        try:
            self.type2 = self.i2.type
        except AttributeError:
            self.type2 = "?"
        if mode is None:
            self.mode = "unknown"
        else:
            self.mode = mode

    def item_str(self, i, t, latex=False):
        if i is None:
            return None
        if isinstance(i, TypeConstructor):
            if latex:
                return "type %s" % i.latex_str()
            else:
                return "type %s" % repr(i)
        elif isinstance(i, str):
            if t is None or t is "?":
                return "'" + i + "'"
            else:
                if latex:
                    return "'%s'/%s" % (i, t.latex_str())
                else:
                    return "'%s'/%s" % (i, repr(t))
        else:
            if t is None or t is "?":
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
        if latex:
            tm_str = '<span style="color:red">Type mismatch</span>'
        else:
            tm_str = "Type mismatch"
        if is_1 is None:
            if is_2 is None:
                return "%s, unknown context (mode: %s)" % (tm_str, self.mode)
            else:
                return "%s on %s (mode: %s)" % (tm_str, is_2, self.mode)
        else:
            if is_2 is None:
                return "%s on %s (mode: %s)" % (tm_str, is_1, self.mode)
            else:
                return "%s: %s and %s conflict (mode: %s)" % (tm_str, is_1, is_2, self.mode)


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

    def fun_arg_check_bool(self, fun, arg):
        return (fun.type.functional() and
                self.type_allowed(fun.type) and
                self.type_allowed(arg.type) and
                self.eq_check(fun.type.left, arg.type))

    def check_type(self, t):
        return (t in self.atomics or t.__class__ in self.nonatomics)

    def unify(self, a, b):
        if not (self.check_type(a) and self.check_type(b)):
            return None
        (result, r_assign) = a.unify(b, self.unify, None)
        return result

    def unify_fa(self, fun, arg):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's type, the argument's type, and the output type.
        If this fails, returns (None, None, None)."""

        if fun.functional():
            a = self.unify(fun.left, arg)
            if a is None:
                return (None, None, None)
            else:
                return (FunType(a, fun.right), a, fun.right)
        else:
            return (None, None, None)

    def fun_arg_check(self, fun, arg):
        if not self.fun_arg_check_bool(fun, arg):
            raise TypeMismatch(fun.type, arg.type, "function-argument combination")

    def eq_check(self, a, b):
        #return (a == b)
        result = self.unify(a,b)
        return (result is not None)

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

    def random_type(self, max_depth, p_terminate_early):
        term = random.random()
        #print(max_depth)
        if max_depth == 0 or term < p_terminate_early:
            #print(term, p_terminate_early, term > p_terminate_early)
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1, p_terminate_early)
            t_class = random.choice(list(self.nonatomics))
            return t_class.random(ctrl_fun)

    def repr_check(self, t):
        return (t == self.type_parser(repr(t)))

    def repr_unify_check(self, t):
        result = self.unify(t, self.type_parser(repr(t)))
        return (result is not None)

    def unify_check(self, t1, t2):
        result = self.unify(t1, t2)
        return (result is not None)

    def parse_unify_check(self, t1, t2):
        return self.unify_check(self.type_parser(t1), self.type_parser(t2))

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




def injective(d):
    """Is `d` an injective assignment?  I.e. does it map any keys onto the same value?"""
    v = d.values()
    v_set = set(v)
    return len(v) == len(v_set)

def invert(d):
    i = dict()
    for k in d.keys():
        if d[k] in i:
            raise Exception("can't invert non-injective dict")
        i[d[k]] = k
    return i

def strengthens(d):
    """Check for any strengthening assignments in `d`.  A strengthening assignment is one that maps a variable to a non-variable."""
    for key in d:
        if not isinstance(d[key], VariableType):
            return True
    return False

def safe_vars(typ, var_list):
    """Returns a mapping from type variables in `typ` to variable names that are safe from collision from `var_list`."""
    unsafe = typ.bound_type_vars()
    base_nums = dict()
    result = dict()
    for base in var_list:
        if base in unsafe:
            base_letter = base.symbol[0]
            if base_letter not in base_nums:
                base_nums[base_letter] = 0
            # TODO this is not very efficient
            vt = VariableType(base_letter, number=base_nums[base_letter])
            while vt in unsafe:
                base_nums[base_letter] += 1
                vt = VariableType(base_letter, number=base_nums[base_letter])
            result[base] = vt
            unsafe = unsafe | {vt}
        else:
            unsafe = unsafe | {base}
    return result

def safe_var_in_type(typ):
    unsafe = typ.bound_type_vars()
    n = 0
    vt = VariableType("X", n)
    while vt in unsafe:
        n += 1
        vt = VariableType("X", n)
    return vt


def make_safe(typ1, typ2, unsafe=None):
    """Return a version of typ1 that is completely safe w.r.t. variables in typ2.

    Note that this will work in either order to avoid variable name collisions, but preserves variable names in typ2 over typ1.
    """
    if unsafe is None:
        unsafe = list()
    else:
        unsafe = list(unsafe)
    assignment = safe_vars(typ2, list(typ1.bound_type_vars()) + unsafe)
    #return (typ1.sub_type_vars(assignment), invert(assignment))
    return typ1.sub_type_vars(assignment)

class UnificationResult(object):
    def __init__(self, principle, t1, t2, mapping):
        self.principle = principle
        self.t1 = t1
        self.t2 = t2
        self.mapping = mapping
        self.trivial = injective(mapping) and not strengthens(mapping)

class PolyTypeSystem(TypeSystem):
    def __init__(self, atomics=None, nonatomics=None):
        super().__init__("polymorphic", atomics=atomics, nonatomics=nonatomics)
        self.add_nonatomic(VariableType)

    def unify(self, t1, t2):
        assignment = dict()
        result = self.unify_details(t1, t2, assignment)
        if result is None:
            return None
        else:
            return result.principle

    def unify_details(self, t1, t2, assignment=None):
        if assignment is None:
            assignment = dict()
        t1safe = make_safe(t1, t2, set(assignment.keys()) | set(assignment.values()))
        (result, r_assign) = self.unify_r(t1safe, t2, assignment)
        if result is None:
            return None
        else:
            return UnificationResult(result, t1, t2, r_assign)

    def unify_r(self, t1, t2, assignment):
        if isinstance(t1, VariableType):
            return t1.unify(t2, self.unify_r, assignment)            
        elif isinstance(t2, VariableType):
            return t2.unify(t1, self.unify_r, assignment)
        else:
            (result, r_assign) = t1.unify(t2, self.unify_r, assignment)
            if result is None:
                return (None, None)
            if len(result) > 1:
                # enforce changes present in assignment on all parts of the result
                # TODO: could do this incrementally?
                l = list()
                for i in range(len(result)-1):
                    l.append(result[i].sub_type_vars(r_assign))
                l.append(result[-1])
                result = result.copy_local(*l)
            return (result, r_assign)

    def unify_fa(self, fun, arg):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's type, the argument's type, and the output type.
        If this fails, returns (None, None, None)."""

        output_var = safe_var_in_type(arg)
        hyp_fun = FunType(arg, output_var)
        result = self.unify_details(hyp_fun, fun) # use reverse order to try to keep variables in fun preferentially
        if result is None: # this will fail if `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            if result.trivial: # no need to introduce spurious alpha renaming
                return (fun, fun.left, fun.right)
            else:
                return (result.principle, result.principle.left, result.principle.right)


    # There's really got to be a better way to do this...
    def alpha_equiv(t1, t2):
        assignment = dict()
        t1safe = make_safe(t1, t2, set(assignment.keys()) | set(assignment.values()))
        (result, r_assign) = self.unify_r(t1safe, t2, assignment)
        return injective(r_assign) and not strengthens(r_assign)

    def random_type(self, max_depth, p_terminate_early, allow_variables=True):
        term = random.random()
        #print(max_depth)
        if max_depth == 0 or term < p_terminate_early:
            #print(term, p_terminate_early, term > p_terminate_early)
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1, p_terminate_early, allow_variables)
            if allow_variables:
                t_class = random.choice(list(self.nonatomics))
            else:
                t_class = random.choice(list(self.nonatomics - {VariableType}))
            return t_class.random(ctrl_fun)

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
    global type_e, type_t, type_n, type_property, type_transitive, basic_system, poly_system

    type_e = BasicType("e", SimpleInfiniteSet("c"))
    type_t = BasicType("t", OntoSet(0,[0,1]))
    type_n = BasicType("n", SimpleIntegerSet())
    type_property = FunType(type_e, type_t)
    type_transitive = FunType(type_e, type_property)
    basic_system = TypeSystem(atomics={type_e, type_t, type_n}, nonatomics={FunType, TupleType})
    #under_system = UnderTypeSystem(atomics={type_e, type_t, type_n, undetermined_type}, nonatomics={FunType, TupleType, UndeterminedType, SetType})
    poly_system = PolyTypeSystem(atomics={type_e, type_t, type_n}, nonatomics={FunType, TupleType, SetType})

setup_type_constants()


import unittest
class TypeTest(unittest.TestCase):
    def setUp(self):
        setup_type_constants()

    def test_parser_simple(self):
        for i in range(0, 1000):
            self.assertTrue(basic_system.repr_check(basic_system.random_type(5, 0.2)))

    def test_parser_poly(self):
        for i in range(0, 1000):
            self.assertTrue(poly_system.repr_check(poly_system.random_type(5, 0.2)))

    def test_parser_poly(self):
        for i in range(0, 1000):
            self.assertTrue(poly_system.repr_unify_check(poly_system.random_type(5, 0.2)))

    def test_var_cases(self):
        self.assertTrue(poly_system.parse_unify_check("e", "e"))
        self.assertTrue(poly_system.parse_unify_check("<e,t>", "<e,t>"))
        self.assertTrue(poly_system.parse_unify_check("X", "X"))
        self.assertTrue(poly_system.parse_unify_check("X", "Y"))
        self.assertTrue(poly_system.parse_unify_check("<X,Y>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<X,X>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,X>,X>", "<<e,Y>,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<<e,X>,Y>,Y>", "<<<X,Z>,Z>,e>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,Y>,<Z,<Z',Z''>>>", "<<X',Y'>,<Y',Z'>>"))

        self.assertFalse(poly_system.parse_unify_check("e", "t"))
        self.assertFalse(poly_system.parse_unify_check("<e,t>", "<e,e>"))
        self.assertFalse(poly_system.parse_unify_check("<<e,X>,X>", "<<X,X>,t>"))
        self.assertFalse(poly_system.parse_unify_check("<<X,X>,<Y,Y>>", "<<e,Z>,<Z,t>>"))


