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
    def __init__(self, finite=False, values=None):
        self.finite = finite
        if values is None:
            values = set()
        else:
            self.domain = set(values)

    def check(self,x):
        if self.finite:
            return (x in self.domain)
        else:
            return self.infcheck(x)

    def __contains__(self, x):
        return self.check(x)

    def infcheck(self, x):
        """Does `x` meet the criteria for being a member of a set if infinite?"""
        raise NotImplementedError(
            "No membership checker for abstract infinite set")

class SimpleInfiniteSet(OntoSet):
    """Contains all strings prefaced with one char prefix."""
    def __init__(self,prefix):
        OntoSet.__init__(self, False, set())
        self.prefix = prefix[0]
        # TODO better error checking

    def infcheck(self,x):
        return (len(x) > 0 and x[0]==prefix)

class SimpleIntegerSet(OntoSet):
    """pretend infinite set for integers, does not implement full infinity"""
    def __init__(self):
        OntoSet.__init__(self, False, set())

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
        """Return a copy of the type with any local properties preserved,
        but *parts substituted appropriately.

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
        """Finds any type variables in the type that are bound.  Reminder:
        in Hindley-Milner, the way it is normally used, all type variables are
        bound. So in practice, this finds all type variables."""
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
        """Substitute type variables in `self` given the mapping in
        `assignment`.

        This does only one-place substitutions, so it won't follow chains if
        there are any."""
        if len(self.type_vars) == 0:
            return self
        l = list()
        dirty = False
        for i in range(len(self)):
            l.append(self[i].sub_type_vars(assignment,
                                                trans_closure=trans_closure))
            if l[i] is not self[i]:
                dirty = True
        if dirty:
            return self.copy_local(*l)
        else:
            return self





    def unify(self, other, unify_control_fun, data):
        """General function for type unification.  Not intended to be called
        directly.  See `TypeSystem.unify`."""
        if not isinstance(self, other.__class__):
            return (None, data)
        if len(self) != len(other):
            return (None, data)
        sig = list()
        for i in range(len(self)):
            (part_result, data) = unify_control_fun(self[i], other[i], data)
            if part_result is None:
                return (None, data)
            sig.append(part_result)
        return (self.copy_local(*sig), data)


class BasicType(TypeConstructor):
    """Class for atomic types.  The core atomic type interface:

    symbol: the name of the type.
    functional(): must return False.

    Extras:
    values: an object implementing the OntoSet interface representing the set
    that this type characterizes.
    """
    def __init__(self, symbol, values=None, name=None):
        super().__init__()
        self.symbol = symbol
        if name is None:
            self.name = symbol
        else:
            self.name = name
        if values is None:
            self.domain = SimpleInfiniteSet("c" + symbol)
        else:
            self.domain = values
        # pre-escape because of the use of "?" for undetermined type
        self.regex = re.compile(re.escape(self.symbol))

    def functional(self):
        return False

    def check(self, x):
        return self.domain.check(x)

    def __eq__(self, other):
        try:
            return self.symbol == other.symbol
        except AttributeError:
            return False

    def copy_local(self):
        return BasicType(self.symbol, self.domain, self.name)

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
            return (None, data)




class FunType(TypeConstructor):
    """Class for non-atomic (functional) binary types.  These characterize a
    set of functions. The core functional type interface:

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
        return ensuremath("\\left\\langle{}%s,%s\\right\\rangle{}"
                            % (self.left.latex_str(), self.right.latex_str()))

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
        return ensuremath("\\left\\{%s\\right\\}"
                                            % self.content_type.latex_str())

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
        return "(%s)" % ",".join([str(self.signature[i])
                                        for i in range(len(self.signature))])

    def latex_str(self):
        return ensuremath("\\left(%s\\right)" % ", ".join(
            [self.signature[i].latex_str()
                                    for i in range(len(self.signature))]))

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
        results = set([self.signature[i].equal(othersig[i])
                                        for i in range(len(self.signature))])
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

########
#
# type assignment code
#
########


# A type assignment is a dict where every entry maps a variable to a type.  That
# type may be itself a variable, or some other type. Each variable determines an
# equivalence class of variables that potentially map to one non-variable type.
#
# Constraints:
#   Type mapping chains are linear (i.e. cannot loop).
#   Variable types are represented in at most one chain.
#   No variable can map to an expression that contains an instance of itself.
#   (The so-called "occurs" check.)
#   Non-variable types should be at the end of chains.

def transitive_add(v, end, assignment):
    """Add something to the end of an existing chain.

    Doesn't check whether `end` is already present.
    """
    visited = set()
    while v in assignment:
        if v in visited or v == end:
            from lamb import meta
            from lamb.meta import logger
            logger.error(
                "breaking loop (v: '%s', end: '%s', visited: '%s', assignment: '%s')"
                % (v, end, visited, assignment))
            break
        visited |= {v}
        next_v = assignment[v]
        assignment[v] = end
        v = next_v
    return assignment

def transitive_find_end(v, assignment):
    """Find the end of an existing chain starting with `v`."""
    # TODO: delete the loop checking from these functions once it's solid
    start_v = v
    visited = set()
    last_v = None
    while isinstance(v, VariableType) and v in assignment:
        if v in visited:
            from lamb import meta
            from lamb.meta import logger
            logger.error(
                "breaking loop (start_v: '%s', v: '%s', visited: '%s', assignment: '%s')"
                % (start_v, v, visited, assignment))
            break
        visited |= {v}
        last_v = v
        v = assignment[v]
    return (v, last_v)

# 
def replace_in_assign(var, value, assign):
    """Replace all instances of `var` in the type assignment with `value`,
    including embedded instances and instances as a key.

    After this, `var` is *gone* from the assignment.  (Don't call this with
    var=value.)
    """
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
            try_subst = assign[k].sub_type_vars({var: value},
                                                        trans_closure=False)
            assign[k] = try_subst
    for d in dellist:
        del assign[d]
    return assign

def type_assignment_set_unsafe(assign, var, value):
    """Sets the end of a chain beginning with `var`.

    if the end of the chain is not a variable type, it is replaced with `value`.
    if it is a variable type, `value` goes on the end.
    if `var` isn't present, it is added.

    This function first substitutes any variables in `value` with the current
    assignment, which could result in failure.
    """
    try_subst = value.sub_type_vars(assign, trans_closure=True)
    if try_subst is None:
        return None
    if try_subst in assign:
        # value converts to a variable already present in the assignment.
        return assign
    if var in assign:
        (principal, prev) = transitive_find_end(var, assign)
        if isinstance(principal, VariableType):
            assign[principal] = value
        else:
            # this is the unsafe part
            assign[prev] = value
    else:
        assign[var] = value
    return assign

def type_assignment_get(assign, var):
    """Return the principal type for `var` in the assignment, or None if there
    is none."""
    (v, prev) = transitive_find_end(var, assign)
    if prev is None:
        return None
    else:
        return v

def union_assignment(assign, var, value):
    """Either add `value` to the assignment, or disjoin it to an existing
    assignment.

    (This will throw an exception if `value` or the existing assignment contain
    variables.)
    """
    cur = type_assignment_get(assign, var)
    if cur is not None and not isinstance(cur, VariableType):
        value = DisjunctiveType.factory(cur, value) # may throw exception
    if value is not None:
        type_assignment_set_unsafe(assign, var, value)
    return assign

def union_assignments(a1, a2):
    """Produce the union of two assignments using disjunctive types."""
    a1 = a1.copy()
    for m in a2:
        union_assignment(a1, m, a2[m])
    return a1

class VariableType(TypeConstructor):
    """A type variable.  Variables are named with X, Y, Z followed by a number
    (or prime symbols).

    A type variable represents a (not-necessarily-finite) set of types."""
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
        self.domain = set()
        self.init_type_vars()

    def internal(self):
        return self.symbol[0] == "I"

    def functional(self):
        """Return True, because there are functions in the set a type variable
        represents.  Particular assignments could rule this out, of course."""
        return True

    def copy_local(self):
        return VariableType(self.symbol, self.number)
    
    def equal(self, other):
        raise NotImplementedError
        return Maybe
    
    # 
    def unify(self, t2, unify_control_fun, assignment):
        """Unify `self` with `t2`.  Getting this right is rather complicated.

        The result is a tuple of a principal type and an assignment.
        The principal type for two (potentially variable) types is the strongest
        type compatible with both. If it fails, the left element of the return
        tuple will be None, and the relevant may be None. This isn't generally
        safe from side-effects on the input assignment.  If The return value
        has `None` as the right element, the input should be discarded.
        """
        if self == t2:
            return (self, assignment)
        # 1. find the principal type in the equivalence class identified by
        #    self.  May return self if there's a loop.
        #    (Other sorts of loops should be ruled out?)
        if self in assignment:
            (start, prev) = transitive_find_end(self, assignment)
        else:
            start = self
            prev = None
        # 2. find the principal type in the equivalence class identified by t2.
        if isinstance(t2, VariableType) and t2 in assignment:
            (t2_principal, t2_prev) = transitive_find_end(t2, assignment)
        else:
            t2_principal = t2
            t2_prev = None
        new_principal = start
        # 3. perform an occurs check -- that is, check for recursive use of
        #    type variables.  (E.g. unifying X with <X,Y>.)
        if PolyTypeSystem.occurs_check(new_principal, t2_principal):
            from lamb import meta
            from lamb.meta import logger
            logger.error(
                "Failed occurs check: can't unify recursive types %s and %s"
                % (new_principal, t2_principal))
            return (None, None)
        # 4. Deal with cases where `start` is a type variable.  This will end
        #    up with the only instance of `start` as a key in the assignment.
        #    (Or no instance, if `start` and `t2_principal` are equivalent.)
        if isinstance(start, VariableType):
            # 4-a. if t2 is not (equivalent to) a type variable itself,
            #      substitute any embedded type variables according to the
            #      assignment. occurs-check situations can arise after this
            #      substitution.  (Could this all be condensed down to one
            #      occurs check?)
            if not isinstance(t2_principal, VariableType):
                t2_principal = t2_principal.sub_type_vars(assignment,
                                                            trans_closure=True)
                if PolyTypeSystem.occurs_check(start, t2_principal):
                    from lamb import meta
                    from lamb.meta import logger
                    logger.error(
                        "Failed occurs check: can't unify recursive types %s and %s"
                        % (new_principal, t2_principal))
                    return (None, None)
            # 4-b. add `start` => `t2_principal` to the assignment.  
            #      We do this by first clearing out `start` entirely from the
            #      assignment and then mapping it directly to `t2_principal`.
            if start != t2_principal:
                assignment = replace_in_assign(start, t2_principal, assignment)
                assignment[start] = t2_principal
                new_principal = t2_principal
        # 5. Deal with cases where `t2_principal` is a type variable.
        if isinstance(t2_principal, VariableType):
            # 5-a. First make sure `start` is consistent with the assignment by
            #      doing any necessary substitutions.
            if not isinstance(start, VariableType):
                start = start.sub_type_vars(assignment, trans_closure=True)
                # TODO: do I need an occurs check here?  Hasn't come up in tons
                # of random testing, but I'm not confident.
            # 5-b. Then, map `t2_principal` to `start` in the assignment.
            #      Note: if both are variables, this step will undo step 4 to
            #      some degree.  Both are necessary because *TODO*
            if t2_principal != start:
                assignment = replace_in_assign(t2_principal, start, assignment)
                assignment[t2_principal] = start
                new_principal = start
        # 6. Deal with cases where neither are type variables, by recursing.
        if not (isinstance(start, VariableType) or isinstance(t2_principal,
                                                                VariableType)):
            new_principal, assignment = unify_control_fun(start, t2_principal,
                                                                    assignment)
            if new_principal is None:
                return (None, None)
        return (new_principal, assignment)

    def find_type_vars(self):
        return set((self,))
    
    def init_type_vars(self):
        # this will trigger on the initial call to TypeConstructor.__init__,
        # need to defer
        if self.number is not None:
            self.type_vars = set((self,))
    
    def sub_type_vars(self, assignment, trans_closure=False):
        """find the principal type, if any, determined by the `assignment` for
        `self.

        If `trans_closure` is true, check full chains, otherwise just check
        immediate assignments.
        """
        if self in assignment:
            x = assignment[self]
            if trans_closure:
                visited = {self}
                while x in assignment:
                    if x in visited:
                        from lamb import meta
                        from lamb.meta import logger
                        logger.error(
                            "breaking loop in substitution (x: '%s', visited: '%s', , assignment: '%s')"
                            % (x, visited, assignment))
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
        """This implements token equality.  This is _not_ semantic equality due
        to type variable binding.
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
    """Special case of a variable type where the type variable is guaranteed to
    be free, i.e. where the identity just doesn't matter.

    Something like <?,?> amounts to <X,Y> where X,Y are free no matter what.
    """
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

class DisjunctiveType(TypeConstructor):
    """Disjunctive types.

    These types represent finite sets of non-polymorphic types.  (Accordingly,
    disjunctions of variable types are disallowed.)"""
    def __init__(self, *type_list, raise_s=None, raise_i=None):
        disjuncts = set()
        for t in type_list:
            if isinstance(t, DisjunctiveType):
                disjuncts.update(t.disjuncts)
            elif len(t.bound_type_vars()) > 0:
                # this constraint is somewhat arbitrary, and could be
                # generalized. But, then unification would be more complicated.
                raise TypeParseError(
                    "Variable types can't be used disjunctively.",
                    raise_s, raise_i)
            else:
                disjuncts.add(t)
        if len(disjuncts) <= 1:
            raise TypeParseError(
                "Disjunctive type must have multiple unique disjuncts",
                raise_s, raise_i)
        self.disjuncts = disjuncts
        # still sort for a canonical ordering
        self.type_list = sorted(self.disjuncts, key=repr)
        super().__init__()
        self.store_functional_info()
        
    def __hash__(self):
        return hash(tuple(self.type_list))
    
    def __eq__(self, other):
        if isinstance(other, DisjunctiveType):
            return self.disjuncts == other.disjuncts
        else:
            return False
        
    def __len__(self):
        return len(self.disjuncts)
    
    def __getitem__(self, i):
        return self.type_list[i]
    
    def __iter__(self):
        return iter(self.type_list)
        
    def __repr__(self):
        return "[" + "|".join([repr(t) for t in self.type_list]) + "]"
    
    def latex_str(self):
        # wrap in curly braces to ensure the brackets don't get swallowed
        return ensuremath("{\\left[%s\\right]}" % "\mid{}".join(
            [self.type_list[i].latex_str()
                                    for i in range(len(self.type_list))]))
    
    # this works if b is a regular type or a disjunctive type.
    def __or__(self, b):
        return DisjunctiveType(self, b)
    
    def __and__(self, b):
        return poly_system.unify(self, b)

    def copy_local(self, *parts):
        return DisjunctiveType(*parts)

    @classmethod
    def factory(cls, *disjuncts):
        """returns a disjunctive type or a non-disjunctive type, as appropriate
        for `disjuncts`.

        `disjuncts`, when turned into a set, is:
           length 0: return None
          length 1: return the content
          length 2: return a DisjunctiveType for the disjuncts.
    
        If multiple disjuncts are DisjunctiveTypes, this could still fail,
        depending on what the union looks like.
        """
        r = set(disjuncts)
        if len(r) == 0:
            return None
        elif len(r) == 1:
            (r,) = r
            return r
        else:
            return DisjunctiveType(*r)

    # test case: tp("[<e,t>|<e,n>|<n,t>]").intersection_point(tp("<X,t>"),
    #                                       types.poly_system.unify_r, dict())
    #               should map X to [e|n].
    def intersection_point(self, b, unify_fun, assignment):
        if b in self.disjuncts:
            return (b, assignment)
        else:
            new_disjuncts = list()
            return_assign = assignment
            # assumption: type variables can't be part of a disjunctive type.
            for d in self.disjuncts:
                tmp_assignment = assignment.copy() # sigh
                (principal, tmp_assignment) = unify_fun(d, b, tmp_assignment)
                # Important note: we discard all the temporary assignments
                # *unless* the type disjunction is eliminated.
                if principal is None:
                    continue
                new_disjuncts.append(principal)
                return_assign = union_assignments(return_assign, tmp_assignment)
            result = self.factory(*new_disjuncts)
            if result is None:
                return (result, assignment)
            else:
                return (result, return_assign)
    
    def store_functional_info(self):
        l_set = set()
        r_set = set()
        # alternative: only set something if all disjuncts are functional?
        for d in self.disjuncts:
            if d.functional():
                l_set |= {d.left}
                r_set |= {d.right}
        self.left = self.factory(*l_set)
        self.right = self.factory(*r_set)

    def functional(self):
        return (self.left is not None)

    # returns a FunType characterizing the set of functional types contained in
    # self.
    def factor_functional_types(self):
        return FunType(self.left, self.right)

    def intersection(self, b, unify_fun, assignment):
        """Calculate the intersection of `self` and type `b`.

        If `b` is a DisjunctiveType, this involves looking at the intersection
        of the types. Otherwise, it involves unifying `b` with the contents of
        self and seeing what is left. Will return some type (not necessarily
        disjunctive) if it succeeds, otherwise None.
    
        Some examples:
            [e|n] intersect e = e
            [e|n] intersect X = [e|n]
            [<e,t>|<n,t>|<e,e>] intersect <X,t> = [<e,t>|<n,t>]
            [e|n] intersect t = None
        """
        if isinstance(b, DisjunctiveType):
            # this relies on type variables not being possible as disjuncts.
            # otherwise, you'd need to use unify to check equality.
            intersection = self.disjuncts & b.disjuncts
            return (self.factory(*intersection), assignment)
        else:
            return self.intersection_point(b, unify_fun, assignment)


    def unify(self, b, unify_control_fun, assignment):
        return self.intersection(b, unify_control_fun, assignment)
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        starting_i = i
        next = parsing.consume_char(s, i, "[")
        if next is None:
            return (None, i)
        else:
            i = next
            signature = []
            while i < len(s) and s[i] != "]":
                (m, i) = parse_control_fun(s, i)
                signature.append(m)
                if s[i] == "]":
                    break
                i = parsing.consume_char(s, i, "|",
                                            "Missing | in disjunctive type")
            i = parsing.consume_char(s, i, "]",
                                            "Unmatched [ in disjunctive type")
            return (DisjunctiveType(*signature, raise_s=s, raise_i=starting_i),
                                                                            i)
    
    @classmethod
    def random(cls, random_ctrl_fun):
        type_len = random.randint(2, random_len_cap)
        args = set()
        success = False
        while not success:
            # a lot of seeds might just not work for this class, so keep
            # trying until we get something sensible
            # TODO: in extremely simple (non-realistic) type systems this could
            # loop indefinitely.
            args = set([random_ctrl_fun() for i in range(0,type_len)])
            try:
                result = DisjunctiveType(*args)
            except TypeParseError:
                #print("retry", repr(args))
                continue
            success = True
        return result

####################
#
# Type systems and various utility stuff.
#
####################


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
        if not atomic in self.atomics:
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

    def parse(self, s):
        return self.type_parser(s)

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
        If it succeeds, it returns a (possibly changed) tuple of the function's
        type, the argument's type, and the output type. If this fails, returns
        (None, None, None)."""

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
            raise TypeMismatch(fun.type, arg.type,
                                            "function-argument combination")

    def eq_check(self, a, b):
        result = self.unify(a,b)
        return (result is not None)

    def type_allowed(self, a):
         return True

    def latex_str(self):
        return "Type system with atomic types: " + ensuremath(", ".join(
                                        [a.latex_str() for a in self.atomics]))

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
            ctrl_fun = lambda *a: self.random_type(max_depth - 1,
                                                            p_terminate_early)
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

########################
#
# Polymorphic type system
#
########################

# first some more basic functions for manipulating and testing assignments.

def injective(d):
    """Is `d` an injective assignment?  I.e. does it map any keys onto the same
    value?"""
    v = d.values()
    v_set = set(v)
    return len(v) == len(v_set)

def invert(d):
    """Try to invert the assignment `d`.  Will throw an exception of the
    assignment is not injective."""
    i = dict()
    for k in d.keys():
        if d[k] in i:
            raise Exception("can't invert non-injective dict")
        i[d[k]] = k
    return i

def strengthens(d):
    """Check for any strengthening assignments in `d`.  A strengthening
    assignment is one that maps a variable to a non-variable."""
    for key in d:
        if not isinstance(d[key], VariableType):
            return True
    return False

def safe_vars(typ, var_list):
    """Returns a mapping from type variables in `typ` to variable names that
    are safe from collision from `var_list`."""
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

def vars_in_env(type_env, keys=False):
    """Where `type_env` is a mapping to types, return all type varaibles found
    in the mapping. If `keys` is true, collect all keys."""
    unsafe = set()
    for k in type_env:
        if keys:
            unsafe |= {k}
        unsafe |= type_env[k].bound_type_vars()
    return unsafe

def safe_var_in_set(unsafe, internal=False):
    """Find a safe type variable relative to set `unsafe`.  

    This will be prefixed with `X` unless `internal`=True, in which case the
    prefix is `I`.
    """
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
    """Return a version of typ1 that is completely safe w.r.t. variables in
    typ2.

    Note that this will work in either order to avoid variable name collisions,
    but preserves variable names in typ2 over typ1.
    """
    if unsafe is None:
        unsafe = list()
    else:
        unsafe = list(unsafe)
    assignment = safe_vars(typ2, list(typ1.bound_type_vars()) + unsafe)
    return typ1.sub_type_vars(assignment)

def compact_type_set(types, unsafe=None):
    """Given some set of types `types`, produce a mapping to more compact
    variable names. Try to keep any lower-numbered type variables.

    If `unsafe` is set, avoid types in `unsafe`.
    """
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
    """Produce a mapping from variables in `types` to fresh type variables.

    if `unsafe` is set, avoid the types in `unsafe`."""
    if unsafe is None:
        unsafe = set()
    mapping = dict()
    for v in types:
        mapping[v] = VariableType.fresh()
    return mapping

class UnificationResult(object):
    """Wrapper class for passing around unification results."""
    def __init__(self, principal, t1, t2, mapping):
        self.principal = principal
        self.t1 = t1
        self.t2 = t2
        self.mapping = mapping
        self.trivial = injective(mapping) and not strengthens(mapping)

    def _repr_html_(self):
        s = "<table>"
        s += ("<tr><td>Principal type:&nbsp;&nbsp; </td><td>%s</td></tr>"
                                % self.principal.latex_str())
        s += ("<tr><td>Inputs: </td><td>%s and %s</td></tr>"
                                % (self.t1.latex_str(), self.t2.latex_str()))
        s += ("<tr><td>Mapping: </td><td>%s</td></tr>"
                                % utils.dict_latex_repr(self.mapping))
        s += "</table>"
        return s

class PolyTypeSystem(TypeSystem):
    """A polymorphic type system.  

    This implements appropriate unification for type variables (in the
    Hindley-Milner type system) and disjunctive types.
    """
    def __init__(self, atomics=None, nonatomics=None):
        self.type_ranking = dict()
        super().__init__("polymorphic", atomics=atomics, nonatomics=nonatomics)
        self.add_nonatomic(VariableType, 10)
        self.add_nonatomic(UnknownType, 10)

    def add_nonatomic(self, t, ranking=0):
        super().add_nonatomic(t)
        self.type_ranking[t] = ranking

    def remove_nonatomic(self, t):
        supr().remove_nonatomic(t)
        del self.type_ranking[t]

    def add_atomic(self, t, ranking=0):
        super().add_atomic(t)
        self.type_ranking[t.__class__] = ranking

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
        """Find the principal type, if any, for `t1` and `t2`.

        If this succeeds, return a UnificationResult."""
        if assignment is None:
            assignment = dict()
        else:
            assignment = assignment.copy() # ugh
        (result, r_assign) = self.unify_r(t1, t2, assignment)
        if result is None:
            return None
        # a principal type has been found, but may not be fully represented by
        # result. This will happen if later parts of one type forced some
        # strengthening of assumptions, and we need to apply the stronger
        # assumption everywhere.
        l = list()
        for i in range(len(result)):
            l.append(result[i].sub_type_vars(r_assign, trans_closure=True))
        result = result.copy_local(*l)
        return UnificationResult(result, t1, t2, r_assign)

    def unify_r(self, t1, t2, assignment):
        """Recursive unification of `t1` and `t2` given some assignment.

        This is not really intended to be called directly; see comments in
        `unify_details` for more information.  Call `unify` or
        `unify_detail`."""
        if self.occurs_check(t1, t2):
            from lamb import meta
            from lamb.meta import logger
            logger.error(
                "Failed occurs check: can't unify recursive types %s and %s"
                % (t1,t2))
            return (None, assignment)
        if self.type_ranking[t1.__class__] <= self.type_ranking[t2.__class__]:
            return t2.unify(t1, self.unify_r, assignment)
        else:
            return t1.unify(t2, self.unify_r, assignment)

    def unify_fr(self, fun, ret, assignment=None):
        """Find principal types if `ret` is a return value for `fun`.  

        Returns a triple of the principal types of the function, its left type,
        and its right type.  Returns (None, None, None) on failure."""
        if assignment is None:
            assignment = dict()
        input_var = VariableType.fresh()
        hyp_fun = FunType(input_var, ret)
        result = self.unify_details(hyp_fun, fun, assignment=assignment)
        if result is None: # `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            return (result.principal, result.principal.left,
                                                    result.principal.right)

    def unify_fa(self, fun, arg, assignment=None):
        """Find principal types if `ret` is a return value for `fun`.  

        Returns a triple of the principal types of the function, its left type,
        and its right type.  Returns (None, None, None) on failure."""
        if assignment is None:
            assignment = dict()
        output_var = VariableType.fresh()
        hyp_fun = FunType(arg, output_var)
        result = self.unify_details(hyp_fun, fun, assignment=assignment)
        if result is None: # `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            return (result.principal, result.principal.left,
                                                        result.principal.right)

    def fun_arg_check_bool(self, fun, arg):
        f, l, r = self.unify_fa(fun.type, arg.type)
        return f is not None

    # There's really got to be a better way to do this...
    def alpha_equiv(self, t1, t2):
        """Are `t1` and `t2` alpha equivalents of each other?"""
        assignment = dict()
        t1safe = make_safe(t1, t2, set(assignment.keys())
                                                    | set(assignment.values()))
        (result, r_assign) = self.unify_r(t1safe, t2, assignment)
        return injective(r_assign) and not strengthens(r_assign)

    def compact_type_vars(self, t1, unsafe=None):
        """Compact the type variables in `t1` so as to make them more
        readable."""
        types = t1.bound_type_vars()
        mapping = compact_type_set(types, unsafe)
        return t1.sub_type_vars(mapping)

    def unify_sym_check(self, t1, t2):
        """Utility function for testing that unification obeys symmetry.

        Return true if `t1` and `t2` produce the same unification result
        (including failure) in both directions."""
        from lamb.meta import logger
        oldlevel = logger.level
        logger.setLevel(logging.CRITICAL) # suppress occurs check errors
        r1 = self.unify(t1, t2)
        r2 = self.unify(t2, t1)
        logger.setLevel(oldlevel)
        if ((r1 is None) and (r2 is None)):
            return True
        if ((r1 is None) or (r2 is None)):
            print("Unify failed in one direction, results '%s' and '%s'"
                                                    % (repr(r1), repr(r2)))
            return False
        result = self.alpha_equiv(r1, r2)
        return result

    def random_from_class(self, cls, max_depth=2, p_terminate_early=0.2,
                                                    allow_variables=False):
        return cls.random(self.random_ctrl(max_depth=max_depth,
                                           p_terminate_early=p_terminate_early,
                                           allow_variables=allow_variables))

    def random_ctrl(self, max_depth=2, p_terminate_early=0.2,
                                                    allow_variables=False):
        return lambda *a: self.random_type(max_depth - 1,
                                            p_terminate_early, allow_variables)

    def random_type(self, max_depth, p_terminate_early, allow_variables=True,
                                                        allow_disjunction=True):
        """Generate a random type of `max_depth`."""
        term = random.random()
        if max_depth == 0 or term < p_terminate_early:
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1,
                                            p_terminate_early, allow_variables)
            options = self.nonatomics - {UnknownType}
            if not allow_variables:
                options -= {VariableType}
            if not allow_disjunction:
                options -= {DisjunctiveType}
            t_class = random.choice(list(options))
            return t_class.random(ctrl_fun)

    def random_variable_type(self, max_depth, p_terminate_early):
        """Generate a random type of `max_depth`; use only variable types in
        place of atomic types."""
        term = random.random()
        ctrl_fun = lambda *a: self.random_variable_type(max_depth - 1,
                                                            p_terminate_early)
        if max_depth == 0 or term < p_terminate_early:
            # choose a variable type
            t = VariableType.random(ctrl_fun)
            return t
        else:
            # choose a non-variable type and generate a random instantiation
            t_class = random.choice(
                    list(self.nonatomics - {VariableType, DisjunctiveType}))
            return t_class.random(ctrl_fun)

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
            if t is None or t == "?":
                return "'" + i + "'"
            else:
                if latex:
                    return "'%s'/%s" % (i, t.latex_str())
                else:
                    return "'%s'/%s" % (i, repr(t))
        else:
            if t is None or t == "?":
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
                return "%s, unknown context (%s)" % (tm_str, self.mode)
            else:
                return "%s on %s (%s)" % (tm_str, is_2, self.mode)
        else:
            if is_2 is None:
                return "%s on %s (%s)" % (tm_str, is_1, self.mode)
            else:
                return ("%s: %s and %s conflict (%s)"
                                            % (tm_str, is_1, is_2, self.mode))

    def _repr_html_(self):
        return self.latex_str()

    def __repr__(self):
        return self.__str__()


class TypeParseError(Exception):
    """Exception for when types can't be parsed or generated correctly."""
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
            return "%s at point '%s!here!%s'" % (self.msg, self.s[0:self.i],
                                                            self.s[self.i:])


def setup_type_constants():
    global type_e, type_t, type_n, type_property, type_transitive
    global basic_system, poly_system

    type_e = BasicType("e", SimpleInfiniteSet("c"))
    type_t = BasicType("t", OntoSet(False, [0,1]))
    type_n = BasicType("n", SimpleIntegerSet())
    type_property = FunType(type_e, type_t)
    type_transitive = FunType(type_e, type_property)
    basic_system = TypeSystem(atomics={type_e, type_t, type_n},
                              nonatomics={FunType, TupleType})
    poly_system = PolyTypeSystem(atomics={type_e, type_t, type_n},
                                 nonatomics={FunType, TupleType, SetType})
    poly_system.add_nonatomic(DisjunctiveType, 1)

setup_type_constants()


import unittest
class TypeTest(unittest.TestCase):
    def setUp(self):
        setup_type_constants()

    def test_parser_simple(self):
        for i in range(0, 1000):
            self.assertTrue(
                    basic_system.repr_check(basic_system.random_type(5, 0.2)))

    def test_parser_poly(self):
        for i in range(0, 1000):
            self.assertTrue(
                    poly_system.repr_check(poly_system.random_type(5, 0.2)))

    def test_parser_poly_unify(self):
        for i in range(0, 1000):
            self.assertTrue(
                poly_system.repr_unify_check(poly_system.random_type(5, 0.2)))

    def test_parser_poly_varsonly(self):
        for i in range(0, 1000):
            self.assertTrue(
                poly_system.repr_unify_check(
                                    poly_system.random_variable_type(5, 0.2)))

    def test_symmetry(self):
        """Ensure that unify is symmetric for variable types."""
        for depth in range (1,5): # this checks at the same depth for t1 and t2, and so can miss things.
            for i in range(0, 500):
                t1 = poly_system.random_variable_type(depth, 0.2)
                t2 = poly_system.random_variable_type(depth, 0.2)
                result = poly_system.unify_sym_check(t1, t2)
                if (not result):
                    print(
                        "Symmetry check failed: '%s' and '%s'."
                        % (repr(t1), repr(t2)))
                self.assertTrue(result)
        for depth1 in range (1,2):
            for depth2 in range (1,2):
                for i in range(0, 500):
                    t1 = poly_system.random_variable_type(depth1, 0.2)
                    t2 = poly_system.random_variable_type(depth2, 0.2)
                    result = poly_system.unify_sym_check(t1, t2)
                    if (not result):
                        print("Symmetry check failed: '%s' and '%s'."
                                % (repr(t1), repr(t2)))
                    self.assertTrue(result)

    def test_symmetry_general(self):
        for depth1 in range (1,2):
            for depth2 in range (1,2):
                for i in range(0, 500):
                    t1 = poly_system.random_type(depth1, 0.2)
                    t2 = poly_system.random_type(depth2, 0.2)
                    result = poly_system.unify_sym_check(t1, t2)
                    if (not result):
                        print("Symmetry check failed: '%s' and '%s'."
                                % (repr(t1), repr(t2)))
                    self.assertTrue(result)


    def test_disjunctive_cases(self):
        self.assertTrue(poly_system.parse_unify_check("[e|t]", "[t|e]"))
        self.assertTrue(poly_system.parse_unify_check("[e|t]", "[t|e]"))
        self.assertTrue(poly_system.parse("[e|t]") & poly_system.parse("[t|n]")
                        == poly_system.parse("t"))
        self.assertTrue(poly_system.parse("[e|t]") | poly_system.parse("[t|n]")
                        == poly_system.parse("[e|t|n]"))
        self.assertTrue((poly_system.parse("[e|t]")
                                & poly_system.parse("[<e,t>|n]")) is None)

        with self.assertRaises(TypeParseError): poly_system.parse("[e|e]")
        with self.assertRaises(TypeParseError): poly_system.parse("[e]")
        with self.assertRaises(TypeParseError): poly_system.parse("[X|e]")
        with self.assertRaises(TypeParseError): poly_system.parse("[e|<e,X>]")

    def test_var_cases(self):
        self.assertTrue(poly_system.parse_unify_check("e", "e"))
        self.assertTrue(poly_system.parse_unify_check("<e,t>", "<e,t>"))
        self.assertTrue(poly_system.parse_unify_check("X", "X"))
        self.assertTrue(poly_system.parse_unify_check("X", "Y"))
        self.assertTrue(poly_system.parse_unify_check("<X,Y>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<X,X>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,X>,X>", "<<e,Y>,Z>"))
        self.assertTrue(poly_system.parse_unify_check(
                                            "<<<e,X>,Y>,Y>", "<<<X,Z>,Z>,e>"))
        self.assertTrue(poly_system.parse_unify_check(
                                "<<X,Y>,<Z,<Z',Z''>>>", "<<X',Y'>,<Y',Z'''>>"))

        self.assertFalse(poly_system.parse_unify_check("e", "t"))
        self.assertFalse(poly_system.parse_unify_check("<e,t>", "<e,e>"))
        self.assertFalse(poly_system.parse_unify_check(
                                            "<<e,X>,X>", "<<Y,Y>,t>"))
        self.assertFalse(poly_system.parse_unify_check(
                                            "<<X,X>,<Y,Y>>", "<<e,Z>,<Z,t>>"))

        # some complicated occurs check cases discovered via random search
        from lamb.meta import logger
        oldlevel = logger.level
        logger.setLevel(logging.CRITICAL) # suppress occurs check errors
        self.assertTrue(poly_system.unify(
                                poly_system.parse("<X,<X5,Y5>>"),
                                poly_system.parse("<X5,X>"))
                        == None)
        self.assertTrue(poly_system.unify(
                                poly_system.parse("<X5,X>"),
                                poly_system.parse("<X,<X5,Y5>>"))
                        == None)
        self.assertTrue(poly_system.unify(
                            poly_system.parse("<X',X''>"),
                            poly_system.parse("<X'',{(<X',Y''>,{Z'''},Z10)}>"))
                        == None)
        self.assertTrue(poly_system.unify(
                            poly_system.parse("<X'',{(<X',Y''>,{Z'''},Z10)}>"),
                            poly_system.parse("<X',X''>"))
                        == None)
        logger.setLevel(oldlevel)


