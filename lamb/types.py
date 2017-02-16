#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re, random
from numbers import Number
from lamb import utils, parsing
from lamb.utils import *
import logging

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
        self.unify_source = None
        self.generic = False
        self.init_type_vars()

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
        raise NotImplementedError

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        raise NotImplementedError

    @classmethod
    def random(cls, random_ctrl_fun):
        print(repr(cls))
        raise NotImplementedError

    def find_type_vars(self):
        """Finds any type variables in the type that are bound.  Reminder: in Hindley-Milner, the way it is normally used, all type variables are bound.
        So in practice, this finds all type variables."""
        accum = set()
        for part in iter(self):
            accum.update(part.find_type_vars())
        return accum

    def bound_type_vars(self):
        return self.type_vars

    def init_type_vars(self):
        accum = set()
        for part in iter(self):
            accum.update(part.type_vars)
        self.type_vars = accum



    def sub_type_vars(self, assignment, trans_closure=False):
        """Substitute type variables in `self` given the mapping in `assignment`.

        This does only one-place substitutions, so it won't follow chains if there are any."""
        if len(self.type_vars) == 0:
            return self
        l = list()
        dirty = False
        for i in range(len(self)):
            l.append(self[i].sub_type_vars(assignment,trans_closure=trans_closure))
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
        super().__init__()
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

    def __repr__(self):
        return "%s" % self.symbol

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self):
        return ensuremath(repr(self))

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

    def __repr__(self):
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

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self):
        return ensuremath("\\left\\langle{}%s,%s\\right\\rangle{}" % (self.left.latex_str(), self.right.latex_str()))

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

    def __repr__(self):
        return "{%s}" % repr(self.content_type)

    def latex_str(self):
        return ensuremath("\\left\\{%s\\right\\}" % self.content_type.latex_str())

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
        #if len(signature) == 0:
        #    raise ValueError("Tuple type can't be 0 length")
        self.signature = tuple(signature)
        TypeConstructor.__init__(self)

    def copy_local(self, *sig):
        return TupleType(*sig)

    def functional(self):
        return False

    def check(self, x):
        raise NotImplementedError()

    def __repr__(self):
        return "(%s)" % ",".join([str(self.signature[i]) for i in range(len(self.signature))])

    def latex_str(self):
        return ensuremath("\\left(%s\\right)" % ", ".join([self.signature[i].latex_str() for i in range(len(self.signature))]))

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

    def __call__(self, other):
        return FunType(self, other)

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "(")
        if next is None:
            return (None, i)
        else:
            i = next
            signature = []
            while i < len(s) and s[i] != ")":
                (m, i) = parse_control_fun(s, i)
                signature.append(m)
                if s[i] == ")":
                    break
                i = parsing.consume_char(s, i, ",", "Missing comma in tuple")
            i = parsing.consume_char(s, i, ")", "Unmatched ( in tuple type")
            return (TupleType(*signature), i)       

    @classmethod
    def random(cls, random_ctrl_fun):
        tuple_len = random.randint(0, random_len_cap)
        args = tuple([random_ctrl_fun() for i in range(0,tuple_len)])
        return TupleType(*args)

vartype_regex_str = r"[XYZ]('+|([0-9]*))"
vartype_regex = re.compile(vartype_regex_str)
vartype_regex_full = re.compile( "^" + vartype_regex_str + "$")

def is_vartype_symbol(x):
    m = vartype_regex_full.match(x)
    if m:
        return True
    else:
        return False

def parse_vartype(x):
    m = vartype_regex_full.match(x)
    if not m:
        return (None, None)
    symbol = x[0]
    if len(x) > 1:
        if x[1] == "'":
            return (symbol, len(x)-1)
        else:
            return (symbol, int(x[1:]))
    else:
        return (symbol, 0)

def transitive_add(v, end, assignment):
    visited = set()
    while v in assignment:
        if v in visited or v == end:
            from lamb import meta
            from lamb.meta import logger
            logger.error("breaking loop (v: '%s', end: '%s', visited: '%s', assignment: '%s')" % (v, end, visited, assignment))
            break
        visited |= {v}
        next_v = assignment[v]
        assignment[v] = end
        v = next_v
    return assignment

def transitive_find_end(v, assignment):
    # TODO: delete the loop checking from these functions once it's solid
    start_v = v
    visited = set()
    last_v = None
    while isinstance(v, VariableType) and v in assignment:
        if v in visited:
            from lamb import meta
            from lamb.meta import logger
            logger.error("breaking loop (start_v: '%s', v: '%s', visited: '%s', assignment: '%s')" % (start_v, v, visited, assignment))
            break
        visited |= {v}
        last_v = v
        v = assignment[v]
    return (v, last_v)

def replace_in_assign(var, value, assign):
    #print("input: %s, var: %s, value: %s" %  (assign, var, value))
    if var in assign:
        if isinstance(value, VariableType):
            if value in assign:
                print("%s already in assignment %s?" % (value, assign))
            if value != assign[var]:
                assign[value] = assign[var]
            else:
                del assign[value]
        del assign[var]
    dellist = list()
    for k in assign.keys():
        if isinstance(assign[k], VariableType) and assign[k] == var:
            if k != value:
                assign[k] = value
            else:
                dellist.append(k)
        else:
            try_subst = assign[k].sub_type_vars({var: value}, trans_closure=False)
            assign[k] = try_subst
    for d in dellist:
        del assign[d]
    return assign

class VariableType(TypeConstructor):
    max_id = 0

    def __init__(self, symbol, number=None):
        self.number = None
        super().__init__()
        if number is not None:
            self.symbol = symbol[0] 
            self.number = number
        else:
            (symbol, number) = parse_vartype(symbol)
            if symbol is None:
                raise parsing.ParseError("Can't parse variable type", s=symbol)
            self.symbol = symbol
            self.number = number
        if self.number > VariableType.max_id:
            VariableType.max_id = self.number
        self.name = symbol
        self.values = set()
        self.init_type_vars()

    def internal(self):
        return self.symbol[0] == "I"

    def functional(self):
        return False # ???

    def copy_local(self):
        return VariableType(self.symbol, self.number)
    
    def equal(self, other):
        raise NotImplementedError
        return Maybe
    
    def unify(self, t2, unify_control_fun, assignment):
        if self == t2:
            return (self, assignment)
        # find the principal type in the equivalence class identified by self.  May return self if there's a loop.
        #  (Other sorts of loops should be ruled out?)
        if self in assignment:
            (start, prev) = transitive_find_end(self, assignment)
        else:
            start = self
            prev = None
        # find the principal type in the equivalence class identified by t2.
        if isinstance(t2, VariableType) and t2 in assignment:
            (t2_principal, t2_prev) = transitive_find_end(t2, assignment)
        else:
            t2_principal = t2
            t2_prev = None
        new_principal = start
        if PolyTypeSystem.occurs_check(new_principal, t2_principal):
            from lamb import meta
            from lamb.meta import logger
            logger.error("Failed occurs check: can't unify recursive types %s and %s" % (new_principal, t2_principal))
            return (None, None)
        if isinstance(start, VariableType):
            if not isinstance(t2_principal, VariableType):
                t2_principal = t2_principal.sub_type_vars(assignment, trans_closure=True)
            assignment = replace_in_assign(start, t2_principal, assignment)
            if start != t2_principal:
                assignment[start] = t2_principal
                new_principal = t2_principal
        if isinstance(t2_principal, VariableType):
            if not isinstance(start, VariableType):
                start = start.sub_type_vars(assignment, trans_closure=True)
            assignment = replace_in_assign(t2_principal, start, assignment)
            if t2_principal != start:
                assignment[t2_principal] = start
                new_principal = start
        if not (isinstance(start, VariableType) or isinstance(t2_principal, VariableType)):
            new_principal, assignment = unify_control_fun(start, t2_principal, assignment)
            if new_principal is None:
                return (None, None)
        return (new_principal, assignment)

    def find_type_vars(self):
        return set((self,))
    
    def init_type_vars(self):
        # this will trigger on the initial call to TypeConstructor.__init__, need to defer
        if self.number is not None:
            self.type_vars = set((self,))
        
    def sub_type_vars(self, assignment, trans_closure=False):
        if self in assignment:
            x = assignment[self]
            if trans_closure:
                visited = {self}
                while x in assignment:
                    if x in visited:
                        from lamb import meta
                        from lamb.meta import logger
                        logger.error("breaking loop in substitution (x: '%s', visited: '%s', , assignment: '%s')" % (x, visited, assignment))
                        break
                    visited |= {x}
                    x = assignment[x]
            return x
        else:
            return self

    def key_str(self):
        return self.symbol + str(self.number)

    def __hash__(self):
        return hash(self.key_str())

    def __eq__(self, other):
        """This implements token equality.  This is _not_ semantic equality due to type variable binding.
        """
        if isinstance(other, VariableType):
            return self.symbol == other.symbol and self.number == other.number
        else:
            return False
    
    def __repr__(self):
        if self.number > 3:
            return self.symbol + str(self.number)
        else:
            return self.symbol + "'" * self.number
    
    def latex_str(self):
        if self.number > 3:
            return ensuremath(self.symbol + "_{" + str(self.number) + "}")
        else:
            return ensuremath(self.symbol + "'" * self.number)
    
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
        primes = random.randint(0, 5)
        var = random.choice(("X", "Y", "Z"))
        return VariableType(var, number=primes)

    @classmethod
    def fresh(cls):
        return VariableType("I", number=cls.max_id + 1)


# ensure that this gets reset on reload
VariableType.max_id = 0

class UnknownType(VariableType):
    max_identifier = 0
    def __init__(self, force_num=None):
        if force_num is None:
            UnknownType.max_identifier += 1
            self.identifier = UnknownType.max_identifier
        else:
            self.identifier = force_num
        super().__init__("?", number=self.identifier)

    def __repr__(self):
        return "?"

    def latex_str(self):
        return ensuremath("?")
    
    def copy_local(self):
        return UnknownType(force_num=self.identifier)
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        new_i = parsing.consume_char(s, i, "?")
        if new_i is None:
            return (None, i)
        else:
            return (UnknownType(), new_i)

    @classmethod
    def random(cls, random_ctrl_fun):
        return UnknownType()

    @classmethod
    def fresh(cls):
        return UnknownType()



def flexible_equal(t1, t2):
    result = t1.equal(t2)
    if result == Maybe or result == True:
        return True
    else:
        return False



class TypeMismatch(Exception):
    """Exception for type mismatches of all sorts."""
    def __init__(self, i1, i2, mode=None):
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

    def _repr_html_(self):
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

    def unify_ar(self, arg, ret):
        return FunType(arg, ret)

    def unify_fr(self, fun, ret):
        if fun.functional():
            r = self.unify(fun.right, ret)
            if r is None:
                return (None, None, None)
            else:
                return (fun, fun.left, r)
        else:
            return (None, None, None)

    def unify_fa(self, fun, arg):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's type, the argument's type, and the output type.
        If this fails, returns (None, None, None)."""

        if fun.functional():
            a = self.unify(fun.left, arg)
            if a is None:
                return (None, None, None)
            else:
                return (fun, a, fun.right)
        else:
            return (None, None, None)

    def fun_arg_check(self, fun, arg):
        if not self.fun_arg_check_bool(fun, arg):
            raise TypeMismatch(fun.type, arg.type, "function-argument combination")

    def eq_check(self, a, b):
        result = self.unify(a,b)
        return (result is not None)

    def type_allowed(self, a):
         return True

    def latex_str(self):
        return "Type system with atomic types: " + ensuremath(", ".join([a.latex_str() for a in self.atomics]))


    def _repr_latex_(self):
        return self.latex_str()

    def random_type(self, max_depth, p_terminate_early):
        term = random.random()
        if max_depth == 0 or term < p_terminate_early:
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

def vars_in_env(type_env):
    unsafe = set()
    for k in type_env:
        unsafe = unsafe | type_env[k].bound_type_vars()
    return unsafe

def vars_in_mapping(type_mapping):
    result = set()
    for m in type_mapping:
        result = result | {m}
        result = result | type_mapping[m].bound_type_vars()
    return result

def safe_var_in_set(unsafe, internal=False):
    n = 0
    if internal:
        symbol = "I"
    else:
        symbol = "X"
    vt = VariableType(symbol, n)
    while vt in unsafe:
        n += 1
        vt = VariableType(symbol, n)
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
    return typ1.sub_type_vars(assignment)

def compact_type_set(types, unsafe=None):
    if unsafe is None:
        unsafe = set()
    remap = list()
    keep = set()
    mapping = dict()
    for t in types:
        if t.number > 3 or t.symbol == "I" or t.symbol == "?":
            remap.append(t)
        else:
            keep.add(t)
    remap.sort(key=VariableType.key_str) # for deterministic behavior
    for t in remap:
        m = safe_var_in_set(keep | unsafe)
        assert t not in m
        mapping[t] = m
        keep.add(m)
    return mapping

def freshen_type_set(types, unsafe=None):
    if unsafe is None:
        unsafe = set()
    mapping = dict()
    for v in types:
        mapping[v] = VariableType.fresh()
    return mapping

class UnificationResult(object):
    def __init__(self, principal, t1, t2, mapping):
        self.principal = principal
        self.t1 = t1
        self.t2 = t2
        self.mapping = mapping
        self.trivial = injective(mapping) and not strengthens(mapping)

    def _repr_html_(self):
        s = "<table>"
        s += "<tr><td>Principal type:&nbsp;&nbsp; </td><td>%s</td></tr>" % self.principal.latex_str()
        s += "<tr><td>Inputs: </td><td>%s and %s</td></tr>" % (self.t1.latex_str(), self.t2.latex_str())
        s += "<tr><td>Mapping: </td><td>%s</td></tr>" % utils.dict_latex_repr(self.mapping)
        s += "</table>"
        return s


class PolyTypeSystem(TypeSystem):
    def __init__(self, atomics=None, nonatomics=None):
        super().__init__("polymorphic", atomics=atomics, nonatomics=nonatomics)
        self.add_nonatomic(VariableType)
        self.add_nonatomic(UnknownType)

    def unify(self, t1, t2, assignment=None):
        assignment = dict()
        result = self.unify_details(t1, t2, assignment=assignment)
        if result is None:
            return None
        else:
            return result.principal

    @classmethod
    def occurs_check(self, t1, t2):
        if isinstance(t1, VariableType) and not isinstance(t2, VariableType):
            return t1 in t2.bound_type_vars()
        if isinstance(t2, VariableType) and not isinstance(t1, VariableType):
            return t2 in t1.bound_type_vars()
        return False

    def unify_details(self, t1, t2, assignment=None):
        if assignment is None:
            assignment = dict()
        else:
            assignment = assignment.copy() # ugh
        (result, r_assign) = self.unify_r(t1, t2, assignment)
        if result is None:
            return None
        # a principal type has been found, but may not be fully represented by result.
        # enforce the mapping everywhere in result.
        l = list()
        for i in range(len(result)):
            l.append(result[i].sub_type_vars(r_assign, trans_closure=True))
        result = result.copy_local(*l)
        return UnificationResult(result, t1, t2, r_assign)

    def unify_r(self, t1, t2, assignment):
        # nearly the same as for strict types: just enforces that if either type is a variable, we call
        # that type's unify function (since only it knows what to do with variables.)
        if self.occurs_check(t1, t2):
            from lamb import meta
            from lamb.meta import logger
            logger.error("Failed occurs check: can't unify recursive types %s and %s" % (t1,t2))
            return (None, None)
        if isinstance(t1, VariableType):
            if isinstance(t2, VariableType):
                return t2.unify(t1, self.unify_r, assignment)
            else:
                return t1.unify(t2, self.unify_r, assignment)            
        elif isinstance(t2, VariableType):
            return t2.unify(t1, self.unify_r, assignment)
        else:
            (result, r_assign) = t1.unify(t2, self.unify_r, assignment)
            if result is None:
                return (None, None)
            return (result, r_assign)

    def unify_fr(self, fun, ret, assignment=None):
        if assignment is None:
            assignment = dict()
        input_var = VariableType.fresh()
        hyp_fun = FunType(input_var, ret)
        result = self.unify_details(hyp_fun, fun, assignment=assignment)
        if result is None: # this will fail if `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            return (result.principal, result.principal.left, result.principal.right)


    def unify_fa(self, fun, arg, assignment=None):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's type, the argument's type, and the output type.
        If this fails, returns (None, None, None)."""

        if assignment is None:
            assignment = dict()
        output_var = VariableType.fresh()
        hyp_fun = FunType(arg, output_var)
        result = self.unify_details(hyp_fun, fun, assignment=assignment)
        if result is None: # this will fail if `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            return (result.principal, result.principal.left, result.principal.right)

    # There's really got to be a better way to do this...
    def alpha_equiv(self, t1, t2):
        assignment = dict()
        t1safe = make_safe(t1, t2, set(assignment.keys()) | set(assignment.values()))
        (result, r_assign) = self.unify_r(t1safe, t2, assignment)
        return injective(r_assign) and not strengthens(r_assign)

    def compact_type_vars(self, t1, unsafe=None):
        types = t1.bound_type_vars()
        mapping = compact_type_set(types, unsafe)
        return t1.sub_type_vars(mapping)


    def unify_sym_check(self, t1, t2):
        from lamb.meta import logger
        oldlevel = logger.level
        logger.setLevel(logging.CRITICAL) # suppress occurs check errors
        r1 = self.unify(t1, t2)
        r2 = self.unify(t2, t1)
        logger.setLevel(oldlevel)
        if r1 is None and r2 is None:
            return True
        if (r1 is None or r2 is None):
            return False
        result = self.alpha_equiv(r1, r2)
        if not result:
            print("Symmetry check failed: '%s' and '%s'." % (repr(r1), repr(r1)))
        return result


    def random_type(self, max_depth, p_terminate_early, allow_variables=True):
        term = random.random()
        if max_depth == 0 or term < p_terminate_early:
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1, p_terminate_early, allow_variables)
            if allow_variables:
                t_class = random.choice(list(self.nonatomics - {UnknownType}))
            else:
                t_class = random.choice(list(self.nonatomics - {VariableType, UnknownType}))
            return t_class.random(ctrl_fun)

    def random_variable_type(self, max_depth, p_terminate_early):
        """Use only variable types in place of atomic types"""
        term = random.random()
        ctrl_fun = lambda *a: self.random_variable_type(max_depth - 1, p_terminate_early)
        if max_depth == 0 or term < p_terminate_early:
            # choose a variable type
            t = VariableType.random(ctrl_fun)
            return t
        else:
            # choose a non-variable type and generate a random instantiation of it
            t_class = random.choice(list(self.nonatomics - {VariableType}))
            return t_class.random(ctrl_fun)

class TypeParseError(Exception):
    def __init__(self, msg, s, i):
        self.s = s
        self.i = i
        self.msg = msg

    def __str__(self):
        if self.s == None or self.i == None:
            return self.msg
        if self.i >= len(self.s):
            return "%s at point '%s!here!" % (self.msg, self.s)
        else:
            return "%s at point '%s!here!%s'" % (self.msg, self.s[0:self.i], self.s[self.i:])


def setup_type_constants():
    global type_e, type_t, type_n, type_property, type_transitive, basic_system, poly_system

    type_e = BasicType("e", SimpleInfiniteSet("c"))
    type_t = BasicType("t", OntoSet(0,[0,1]))
    type_n = BasicType("n", SimpleIntegerSet())
    type_property = FunType(type_e, type_t)
    type_transitive = FunType(type_e, type_property)
    basic_system = TypeSystem(atomics={type_e, type_t, type_n}, nonatomics={FunType, TupleType})
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

    def test_parser_poly_unify(self):
        for i in range(0, 1000):
            self.assertTrue(poly_system.repr_unify_check(poly_system.random_type(5, 0.2)))

    def test_parser_poly_varsonly(self):
        for i in range(0, 1000):
            self.assertTrue(poly_system.repr_unify_check(poly_system.random_variable_type(5, 0.2)))

    def test_symmetry(self):
        """Ensure that unify is symmetric for variable types."""
        for depth in range (1,5):
            for i in range(0, 500):
                t1 = poly_system.random_variable_type(depth, 0.2)
                t2 = poly_system.random_variable_type(depth, 0.2)
                self.assertTrue(poly_system.unify_sym_check(t1, t2))


    def test_var_cases(self):
        self.assertTrue(poly_system.parse_unify_check("e", "e"))
        self.assertTrue(poly_system.parse_unify_check("<e,t>", "<e,t>"))
        self.assertTrue(poly_system.parse_unify_check("X", "X"))
        self.assertTrue(poly_system.parse_unify_check("X", "Y"))
        self.assertTrue(poly_system.parse_unify_check("<X,Y>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<X,X>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,X>,X>", "<<e,Y>,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<<e,X>,Y>,Y>", "<<<X,Z>,Z>,e>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,Y>,<Z,<Z',Z''>>>", "<<X',Y'>,<Y',Z'''>>"))

        self.assertFalse(poly_system.parse_unify_check("e", "t"))
        self.assertFalse(poly_system.parse_unify_check("<e,t>", "<e,e>"))
        self.assertFalse(poly_system.parse_unify_check("<<e,X>,X>", "<<Y,Y>,t>"))
        self.assertFalse(poly_system.parse_unify_check("<<X,X>,<Y,Y>>", "<<e,Z>,<Z,t>>"))


