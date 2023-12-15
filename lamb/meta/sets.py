import random
import lamb
from lamb import types, utils
from .core import derived, registry, get_type_system, BindingOp, TypedExpr, get_sopt
from .core import BinaryGenericEqExpr, SyncatOpExpr, LFun, TypedTerm, to_python_container
from .core import Tuple
from .meta import MetaTerm
from .ply import alphanorm_key
from .boolean import BinaryOrExpr, BinaryAndExpr, ForallUnary, ExistsUnary, false_term, true_term
from lamb.types import type_t, SetType


def setup_operators():
    # type {X}
    registry.add_operator(SetContains, None, None)
    registry.add_operator(SetUnion, None, None)
    registry.add_operator(SetIntersection, None, None)
    registry.add_operator(SetDifference, None, None)
    registry.add_operator(SetEquivalence, None, None)
    registry.add_operator(SetSubset, None, None)
    registry.add_operator(SetProperSubset, None, None)
    registry.add_operator(SetSupset, None, None)
    registry.add_operator(SetProperSupset, None, None)
    registry.add_binding_op(ConditionSet)


def safevar(e, typ=None):
    # a set-specific set of heuristics for finding a good usable/safe variable.
    varname = "x"
    if isinstance(e, ConditionSet):
        varname = e[0].op
        typ = e.type.content_type
    elif isinstance(e, BinarySetOp):
        # e's type isn't guaranteed to give the set type, but we can get it
        # from the operands for all subclasses
        typ = e[0].type.content_type
        if isinstance(e[0], ConditionSet):
            varname = e[0][0].op
        elif isinstance(e[1], ConditionSet):
            varname = e[1][0].op
    elif isinstance(e.type, SetType):
        typ = e.type.content_type

    if typ is None:
        typ = e.type # is this actually useful?
    return TypedTerm(e.find_safe_variable(starting=varname, avoid_bound=False), typ=typ)


class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""

    canonical_name = "Set"
    op_name_uni="Set"
    op_name_latex="Set"
    commutative = False # A bit meaningless, since Set x: Set y: can't occur

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body,
                varname=varname, body_type=types.type_t, assignment=assignment,
                type_check=type_check)
        self.type = SetType(self.vartype)

    def term(self):
        return False

    def latex_str(self, suppress_parens=False, **kwargs):
        # XX this omits some assignment manipulation from superclass, is that
        # correct?
        suppress_sub = True
        if isinstance(self.body, Tuple):
            suppress_sub = False
        body = self.body.latex_str(suppress_parens=suppress_sub, **kwargs)
        return utils.ensuremath(f"\\{{{self[0].latex_str(**kwargs)} \\:|\\: {body}\\}}")

    def __lshift__(self, i):
        return SetContains(i, self)

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname)

    def eliminate(self, **sopts):
        # this is a bit wacky. But for the case where there are no free terms
        # at all, we can convert to a ListedSet via domain enumeration. I'm
        # not sure how generally useful this is...
        if self[0].type.domain.finite and not self.free_terms():
            a = self.scope_assignment()
            sopts['evaluate'] = True
            subs = [elem
                    for elem in self[0].type.domain
                    if self[1]
                            .under_assignment(a | {self.varname : elem})
                            .simplify_all(**sopts) == true_term]
            return derived(
                sset(subs, typ=self.type.content_type),
                self,
                f"ConditionSet => ListedSet (generic on {self.varname})")
        return self

    def simplify(self, **sopts):
        if self[1] == false_term:
            return derived(emptyset(self.type), self, "trivial set condition")

        return self

    def try_adjust_type_local(self, unified_type, derivation_reason,
                                                            assignment, env):
        inner_type = unified_type.content_type
        char = self.to_characteristic()
        sub_var = TypedTerm(self.varname, inner_type)
        new_condition = char.apply(sub_var)
        return self.copy_local(sub_var, new_condition)


class ListedSet(TypedExpr):
    """A ListedSet is a set that simply lists members. The elements can be
    any typed expression, as long as the types are consistent with the whole
    set type. This class allows duplicate expressions, but they have the
    semantics of a regular set -- no multiple membership. Correspondingly, a
    `simplify()` call will remove duplicate members. Note that the constructor
    does *not* do this (though the standard way of creating a set in the
    metalanguage parsing code will have this effect).

    `ListedSet`s are actually very weird objects. The reason is that they
    describe sets over some underlying type domain, but via metalanguage
    objects whose resolution in the type domain is potentially undetermined.
    If every element is a MetaTerm, then their behavior will be like you
    expect. But for any other case, it becomes stranger. Examples:

    * What is the cardinality of `{X_e, Y_e}`? It is at least 1 and at most
      2. The reason is that X and Y could be equal, or could be distinct, but
      either way the set will have an element.
    * Is `{X,Y} <=> {Z}`? If X == Y == Z, then yes, otherwise, no.
    * Is `{X,Y} <=> {X,Y}`? Yes: positive syntactic identity does guarantee
      equivalence.
    * What is `{X, Y} ∩ {Z}`? It could be the empty set (if Z != X and Z != Y),
      or it could be a singleton (if Z == X or Z == Y, where X == Y or X != Y).
    * Pretty much the only intuitive operation is ∪.
    * Is `{X,Y} ⊂ {Z}`? In this case, the answer must be no. If X and Y are
      distinct, this is clear. But if X == Y, then either Z != X (in which case
      there is no overlap at all) or X == Z (in which case the two sets are
      equivalent).
    * Is `{X} ⊂ {Y,Z}`? If X != Y and X == Z, or X != Z and X == Y, then the
      answer is yes. But if X != Y and X != Z, or if X == Y == Z, then the
      answer is no.
    * Difference is a complete mess. What is {X,Y} - {Y}? Well, if X == Y, then
      it's an empty set, otherwise, it's {X}. This means that you can't even
      use syntactic difference safely. {X,Y} - {Y,Z} is even worse, etc.

    General notes:

    * The empty set is typed like other sets. So there is an empty set of type
      {e}, of type {t}, etc. We use {?} as the type for an empty set constructed
      without constraints.
    * A ListedSet whose expression cardinality is 1 is guaranteed to be distinct
      from one whose expression cardinality is 0. But in general, (non-)equality
      for other expressions cardinalities is contingent on the values of the
      expressions. Or in other words: expression cardinality 0/1 are equivalent
      to actual set cardinality, but there are no guarantees for expression
      cardinality > 1.
    * As noted above, a set consisting only of MetaTerms has "normal" behavior
      for naive set theory; expression cardinality = set cardinality, the
      operations and relations can be computed directly on members, etc.
    * One thing that is safe: conversion of a ListedSet into a ConditionSet
      with a disjunction of equalities. But these formulae are often extremely
      unwieldy.
    """
    canonical_name = "ListedSet"
    op_name_uni="ListedSet"
    op_name_latex="ListedSet"
    pre_simplify = True # I think this is formally unnecessary, but it reduces work

    def __init__(self, iterable, typ=None, assignment=None, type_check=True):
        # note! uniqueness is not enforced here.
        # * Syntactic duplicates are removed on `simplify()`
        # * the standard metalanguage parser filters out duplicates in advance
        #   of constructing the ListedSet object.
        args = [self.ensure_typed_expr(a,assignment=assignment) for a in iterable]
        # `typ` here is the content type.
        if len(args) == 0 and typ is None:
            typ = types.UnknownType() # could be a set of anything
        elif typ is None:
            # inherit the type from the first argument
            typ = args[0].type
        for i in range(len(args)):
            # type checking TODO: this isn't right, would need to pick the
            # strongest type
            try:
                args[i] = self.ensure_typed_expr(args[i], typ)
            except types.TypeMismatch as e:
                e.error = "Set elements must have compatible types"
                raise e
        super().__init__("ListedSet", *args)
        self.type = SetType(typ)
        self.set_simplified = False

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, type_check=True):
        # explicit handling of empty sets in order to get the type right
        if len(args) == 0:
            return emptyset(self.type)
        return ListedSet(args)

    @classmethod
    def join(self, l):
        # the constructor already matches the `join` api, and this is just for
        # completeness. It ensures presimplification.
        return sset(l)

    def term(self):
        return False

    def name_of(self, i):
        return f"element {i}"

    def __lshift__(self, i):
        """Use the `<<` operator for set membership."""
        return SetContains(i, self)

    def set(self):
        """Return a python `set` of terms in the ListedSet. This of course uses
        syntactic identity, so while every term will be unique via this
        criteria, it is not guarantted to be the "true" set (unless it consists
        only of `MetaTerm`s)."""
        return set(self.args)

    def sorted_set(self):
        s = self.set()
        return sorted(s, key=alphanorm_key)

    def to_condition_set(self):
        """Convert to a condition set by disjoining members."""
        s = self.simplify()
        var = TypedTerm(s.find_safe_variable(starting="x"), self.type.content_type)
        conditions = [(var % a) for a in s.args]
        # n.b. an empty set gives a ConditionSet that simplifies back to the
        # starting point
        return ConditionSet(var, BinaryOrExpr.join(conditions, empty=false_term))

    def to_characteristic(self):
        s = self.simplify()
        var = TypedTerm(s.find_safe_variable(starting="x"), typ=self.type.content_type)
        # an alternative: go directly to self.to_condition_set().to_characteristic()
        return LFun(var, (var << s))

    def do_simplify(self, **sopts):
        # eliminate any duplicates under syntactic identity when simplifying
        if self.set_simplified or len(self.args) <= 1:
            return self
        args = set(self.args) # remove duplicates, flatten order
        domain = self.type.content_type.domain
        if isinstance(domain, types.DomainSet) and domain.finite and args > domain.domain:
            # if every domain element is present in `args`, drop extraneous
            # elements. E.g. `{True, False, p_t}` simplifies to just {True, False}.
            args = args & domain.domain
        args = sorted(args, key=alphanorm_key) # for a canonical ordering
        result = self.copy_local(*args)
        result.set_simplified = True
        result.derivation = self.derivation # copy any derivation, no changes
        return result

    def simplify(self, **sopts):
        result = self.do_simplify(**sopts)
        if result is self:
            return self
        else:
            return derived(result, self, "ListedSet normalization")

    def __repr__(self):
        if not len(self.args):
            # `{}` parses as the empty set in the metalanguage, but repr(set())
            # gives `set()`.
            # XX currently a type for a set doesn't parse, so we never emit one.
            # However, this will prevent the empty set from having an accurate
            # repr...
            return "{}"
        else:
            return repr(set(self.args))

    def latex_str(self, suppress_parens=False, **kwargs):
        inner = ", ".join([a.latex_str(**kwargs) for a in self.args])
        if not len(self.args):
            # show an explicit type for the empty set
            return utils.ensuremath(f"\\{{{inner}\\}}_{{{self.type.latex_str()}}}")
        else:
            return utils.ensuremath(f"\\{{{inner}\\}}")

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        if len(self.args) == 0:
            # handle empty sets directly.
            # no actual type checking here -- this code shouldn't be reachable
            # unless unify has already succeeded.
            return emptyset(unified_type)

        inner_type = unified_type.content_type
        content = [a.try_adjust_type(inner_type,
                        derivation_reason=derivation_reason,
                        assignment=assignment) for a in self.args]
        result = self.copy_local(*content)
        return result

    @classmethod
    def random(self, ctrl, max_type_depth=1, max_members=6, typ=None, allow_empty=True):
        if typ is None:
            typ = get_type_system().random_type(max_type_depth, 0.5)
        if allow_empty:
            r = range(max_members+1)
        else:
            r = range(max_members+1)[1:]
        length = random.choice(r)
        members = [ctrl(typ=typ) for i in range(length)]
        if not length and random.choice([True, False]):
            # untyped (`{?}`) empty set
            return ListedSet(members)
        else:
            return sset(members, typ=typ)


def emptyset(settype=None):
    """Convenience factory for empty sets"""
    if settype is not None and isinstance(settype, SetType):
        settype = settype.content_type
    return ListedSet(set(), settype)


def sset(iterable, typ=None, assignment=None):
    return ListedSet(iterable, typ=typ, assignment=assignment).do_simplify()


class SetContains(SyncatOpExpr):
    """Binary relation of set membership.  This uses `<<` as the symbol.

    Note that this _does_ support reduction if the set describes its members by
    condition, as set membership is equivalent to saturation of the
    characteristic function of the set."""

    arity = 2
    canonical_name = "<<"
    op_name_uni = "∈"
    # ∈ should work but I was having trouble with it (long ago, recheck)
    op_name_latex = "\\in{}"
    commutative = False

    def __init__(self, arg1, arg2, type_check=True):
        # seems like the best way to do the mutual type checking here?
        # Something more elegant?
        arg1 = self.ensure_typed_expr(arg1)
        arg2 = self.ensure_typed_expr(arg2, SetType(arg1.type))
        arg1 = self.ensure_typed_expr(arg1, arg2.type.content_type)
        super().__init__(type_t, arg1, arg2, tcheck_args=False)

    def copy(self):
        return SetContains(self.args[0], self.args[1])

    def copy_local(self, arg1, arg2, type_check=True):
        return SetContains(arg1, arg2)

    def simplify(self, **sopts):
        if isinstance(self.args[1], ConditionSet):
            derivation = self.derivation
            step = (self.args[1].to_characteristic()(self.args[0])).reduce()
            step.derivation = derivation # suppress the intermediate parts of
                                         # this derivation, if any
            return derived(step, self, "∈ simplification")
        elif self.args[0].meta() and self.args[1].meta():
            # TODO: this should be code on the set object, not here
            result = MetaTerm(self.args[0].op in self.args[1].op)
            return derived(result, self, "∈ simplification")
        elif isinstance(self.args[1], ListedSet) and len(self.args[1]) == 0:
            return derived(false_term, self, "∈ simplification (empty set)")
        elif isinstance(self.args[1], ListedSet) and len(self.args[1]) == 1:
            content, = self.args[1]
            return derived(self.args[0] % content, self,
                                            "∈ simplification (singleton set)")
        elif isinstance(self.args[1], ListedSet) and get_sopt('eliminate_sets', sopts):
            # tends to produce fairly long expressions
            conditions = [(self.args[0] % a) for a in self.args[1]]
            return derived(BinaryOrExpr.join(conditions).simplify_all(**sopts),
                            self,
                            "∈ simplification (set elimination)")
        else:
            # leave other ListedSets as-is for now.
            return self

    @classmethod
    def random(cls, ctrl, max_type_depth=1, typ=None):
        if typ is None:
            typ = get_type_system().random_type(max_type_depth, 0.5)
        return SetContains(ctrl(typ=typ), ctrl(typ=SetType(typ)))


def check_set_types(arg1, arg2, op_name=None):
    if not isinstance(arg1.type, SetType) or not isinstance(arg2.type, SetType):
        if op_name:
            # XX these errors are a bit odd
            raise types.TypeMismatch(arg1, arg2, f"{op_name} requires set types")
        else:
            return None
    ctype = get_type_system().unify(arg1.type.content_type, arg2.type.content_type)
    if ctype is None:
        if op_name:
            raise types.TypeMismatch(arg1, arg2, f"{op_name} requires equivalent set types")
        else:
            return None

    return SetType(ctype)


class BinarySetOp(SyncatOpExpr):
    arity = 2

    def __init__(self, arg1, arg2, op_name, typ=None, type_check=True):
        t = check_set_types(arg1, arg2, op_name=op_name)
        arg1 = self.ensure_typed_expr(arg1, t)
        arg2 = self.ensure_typed_expr(arg2, t)
        if typ is None:
            typ = t
        super().__init__(typ, arg1, arg2, tcheck_args=False)

    @classmethod
    def check_viable(cls, *args):
        if len(args) != 2:
            return False
        return check_set_types(args[0], args[1]) is not None

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, type_check=True):
        # can this technique be pushed into TypedExpr?
        return self.__class__(*args)

    @classmethod
    def random(cls, ctrl, max_type_depth=1, typ=None):
        if cls == BinarySetOp:
            raise NotImplementedError("`random` called on abstract class `BinarySetOp`")
        if typ is None:
            typ = SetType(get_type_system().random_type(max_type_depth, 0.5))
        # XX random ConditionSet
        # s1 = ListedSet.random(ctrl, max_type_depth=max_type_depth, typ=typ)
        # s2 = ListedSet.random(ctrl, max_type_depth=max_type_depth, typ=typ)
        return cls(ctrl(typ=typ), ctrl(typ=typ))

    def try_adjust_type_local(self, typ, reason, assignment, env):
        if self.type == type_t:
            return super().try_adjust_type_local(unified_type,
                                            derivation_reason, assignment, env)
        return self.copy_local(
            self.args[0].try_adjust_type(typ, reason, assignment),
            self.args[1].try_adjust_type(typ, reason, assignment))


class SetUnion(BinarySetOp):
    """Binary operation of set union."""

    canonical_name = "|"
    op_name_uni = "∪"
    op_name_latex = "\\cup{}"
    commutative = True
    associative = True

    # for set operations, we need to run self.simplify() before the
    # recursive steps.
    pre_simplify = True

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Set union")


    def simplify(self, **sopts):
        s1 = to_python_container(self.args[0])
        s2 = to_python_container(self.args[1])
        if s1 is not None and s2 is not None:
            if self.args[0].meta() and self.args[1].meta():
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                return derived(MetaTerm(s1 | s2, typ=self.type), self, "set union")
            else:
                return derived(sset(s1 | s2, typ=self.type.content_type), self, "set union") # blessedly simple
        elif s1 is not None and len(s1) == 0:
            return derived(self.args[1], self, "set union") # {} | X = X
        elif s2 is not None and len(s2) == 0:
            return derived(self.args[0], self, "set union") # X | {} = X

        # for everything except ConditionSets, this tends to make the formula
        # more unwieldy
        if (isinstance(self.args[0], ConditionSet) and isinstance(self.args[1], ConditionSet)
                or get_sopt('eliminate_sets', sopts)):
            var = safevar(self)
            return derived(ConditionSet(var,
                            (var << self.args[0]) | (var << self.args[1])),
                            self,
                            "set union (set elimination)").simplify_all(**sopts)

        return self


class SetIntersection(BinarySetOp):
    """Binary operation of set intersection."""

    canonical_name = "&"
    op_name_uni = "∩"
    op_name_latex = "\\cap{}"
    commutative = True
    associative = True
    pre_simplify = True

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Set intersection")

    def simplify(self, **sopts):
        s1 = to_python_container(self.args[0])
        s2 = to_python_container(self.args[1])
        if s1 is not None and s2 is not None:
            if self.args[0].meta() and self.args[1].meta():
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                return derived(
                    MetaTerm(s1 & s2, typ=self.type),
                    self,
                    "set intersection")

            if s1 <= s2 or s2 <= s1:
                # this case is also also safe: there's no way for expression
                # resolution to expand sets that are in a subset relation.
                # this covers empty set cases.
                return derived(
                    sset(s1 & s2, typ=self.type.content_type),
                    self,
                    "set intersection")

            # otherwise, we need to do some more complicated checks.
            definite = set()
            tbd = set()
            for x in s1 | s2:
                if x in s1 and x in s2:
                    definite.add(x)
                elif not x.meta():
                    tbd.add(x)
                # a MetaTerm that is not in both can be excluded at this point

            definite_expr = sset(definite, typ=self.type.content_type)

            if len(tbd) == 0:
                # everything can be verified
                return derived(definite_expr, self, "set intersection")

            if not get_sopt('eliminate_sets', sopts):
                # everything past here in this branch can get pretty unwieldy
                return self

            var = safevar(self)
            if len(definite) == 0:
                # disjoint, as far as what can be verified goes. That is,
                # anything non-meta is in `tbd`. We can do very little with this
                # case.
                return derived(
                    ConditionSet(var, (var << self.args[0]) & (var << self.args[1])),
                    self,
                    "set intersection (set elimination)")

            tbd = ConditionSet(var, (var << sset(tbd, typ=self.type.content_type)
                                        & (var << sset(s1 - definite, typ=self.type.content_type))
                                        & (var << sset(s2 - definite, typ=self.type.content_type))))
            return derived((definite_expr | tbd), self, "set intersection (set elimination)").simplify_all(**sopts)

        elif s1 is not None and len(s1) == 0:
            return derived(emptyset(self.type), self, "set intersection") # {} & X = {}
        elif s2 is not None and len(s2) == 0:
            return derived(emptyset(self.type), self, "set intersection") # X & {} = {}

        if (isinstance(self.args[0], ConditionSet) and isinstance(self.args[1], ConditionSet)
                or get_sopt('eliminate_sets', sopts)):
            var = safevar(self)
            return derived(
                ConditionSet(var, (var << self.args[0]) & (var << self.args[1])),
                self,
                "set intersection (set elimination)").simplify_all(**sopts)
        return self


class SetDifference(BinarySetOp):
    """Binary operation of set difference."""

    canonical_name = "-"
    op_name_latex = "-"
    commutative = False
    associative = False
    pre_simplify = True

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Set difference")

    def simplify(self, **sopts):
        s1 = to_python_container(self.args[0])
        s2 = to_python_container(self.args[1])
        if s1 is not None and s2 is not None:
            if self.args[0].meta() and self.args[1].meta():
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                return derived(
                    MetaTerm(s1 - s2, typ=self.type),
                    self,
                    "set difference")

            if s2 == s1:
                return derived(emptyset(self.type), self, "set difference")
            # XX implement something more here
            # warning: cases like {X,Y} - {Y} are not safe to simplify under
            # syntactic identity, since if X == Y, then {X} is actually wrong.

        if s1 is not None and len(s1) == 0:
            return derived(emptyset(self.type), self, "set difference") # {} - X = {}
        elif s2 is not None and len(s2) == 0:
            return derived(self.args[0], self, "set difference") # X - {} = X

        if (isinstance(self.args[0], ConditionSet) and isinstance(self.args[1], ConditionSet)
                or get_sopt('eliminate_sets', sopts)):
            var = safevar(self)
            return derived(
                ConditionSet(var, (var << self.args[0]) & (~(var << self.args[1]))),
                self,
                "set difference (set elimination)")#.simplify_all(**sopts)
        return self


class SetEquivalence(BinarySetOp):
    """Binary relation of set equivalence."""

    canonical_name = "<=>"
    op_name_latex = "="
    commutative = True

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Set equivalence", typ=type_t)

    def simplify(self, **sopts):
        s1 = to_python_container(self.args[0])
        s2 = to_python_container(self.args[1])
        if s1 is not None and s2 is not None:
            if len(s1) == 0 or len(s2) == 0:
                # this case is relatively straightforward: we can go simply
                # on the basis of expression cardinality
                return derived(MetaTerm(len(s1) == len(s2)), self, "set equivalence")
            elif s1 == s2:
                # special case syntactic equality, this one is safe
                return derived(true_term, self, "set equivalence")
            elif len(s1) == 1 and len(s2) == 1:
                # special case two singletons
                e1, = s1
                e2, = s2
                return derived(
                    e1.equivalent_to(e2),
                    self,
                    "set equivalence").simplify_all(**sopts)

            # tally up all the potential mismatches
            meta_left = {x for x in s1 - s2 if x.meta()}
            tbd_left = s1 - s2 - meta_left
            meta_right = {x for x in s2 - s1 if x.meta()}
            tbd_right = s1 - s2 - meta_right
            # there's possibly some more fine-grained checks that could be done
            # for mixed meta/non-meta sets
            if len(meta_left) > len(tbd_right):
                # too many MetaTerms in the left for non-MetaTerms on the right
                return derived(false_term, self, "set equivalence")
            if len(meta_right) > len(tbd_left):
                # too many MetaTerms in the right for non-MetaTerms on the left
                return derived(false_term, self, "set equivalence")

            if not get_sopt('eliminate_sets', sopts):
                return self

            var = safevar(self)
            # two special cases where we can safely eliminate some elements of
            # a subset from consideration
            if s1 < s2:
                return derived(
                    ForallUnary(var, ((var << self.args[0]).equivalent_to(
                            var << sset(s2 - s1, typ=self[0].type.content_type)))),
                    self,
                    "set equivalence (set elimination)").simplify_all(**sopts)
            elif s2 < s1:
                return derived(
                    ForallUnary(var, ((var << self.args[1]).equivalent_to(
                            var << sset(s1 - s2, typ=self[0].type.content_type)))),
                    self,
                    "set equivalence (set elimination)").simplify_all(**sopts)

            # at this point, fallthrough to the general case. (Is there anything
            # better that could be done?)

        if (isinstance(self.args[0], ConditionSet) and isinstance(self.args[1], ConditionSet)
                or get_sopt('eliminate_sets', sopts)):
            var = safevar(self)
            return derived(ForallUnary(var, ((var << self.args[0]).equivalent_to(var << self.args[1]))),
                self,
                "set equivalence (set elimination)").simplify_all(**sopts)
        return self

class SetSubset(BinarySetOp):
    """Binary relation of (non-proper) subsethood."""

    canonical_name = "<="
    op_name_uni = "⊆"
    op_name_latex = "\\subseteq{}"
    commutative = False

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Subset", typ=type_t)

    def simplify(self, **sopts):
        old_derivation = self.derivation
        test = derived(self.args[0].equivalent_to(self.args[0] & self.args[1]),
            self, "subset (set elimination)")
        simplified = test.simplify_all(**sopts)
        if simplified is test and not get_sopt('eliminate_sets', sopts):
            # if simplify didn't do anything to this expression, the result is
            # probably not actually simpler than where we started
            self.derived = old_derivation
            return self
        else:
            return simplified

class SetProperSubset(BinarySetOp):
    """Binary relation of proper subsethood."""

    canonical_name = "<"
    op_name_uni = "⊂"
    op_name_latex = "\\subset{}"
    commutative = False

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Proper subset", typ=type_t)

    def simplify(self, **sopts):
        old_derivation = self.derivation
        test = derived(
            ((self.args[0] <= self.args[1]) & (~(self.args[0].equivalent_to(self.args[1])))),
            self,
            "proper subset (set elimination)")
        simplified = test.simplify_all(**sopts)
        if simplified is test and not get_sopt('eliminate_sets', sopts):
            self.derivation = old_derivation
            return self
        else:
            return simplified


class SetSupset(BinarySetOp):
    """Binary relation of (non-proper) supersethood."""

    canonical_name = ">="
    op_name_uni = "⊇"
    op_name_latex = "\\supseteq{}"
    commutative = False

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Superset", typ=type_t)

    def simplify(self, **sopts):
        # always normalize to <=
        return derived(
            SetSubset(self.args[1], self.args[0]),
            self,
            "superset => subset").simplify(**sopts)


class SetProperSupset(BinarySetOp):
    """Binary relation of proper supersethood."""

    canonical_name = ">"
    op_name_uni = "⊃"
    op_name_latex = "\\supset{}"
    commutative = True

    def __init__(self, arg1, arg2, type_check=True):
        super().__init__(arg1, arg2, "Proper superset", typ=type_t)

    def simplify(self, **sopts):
        # always normalize to <
        return derived(
            SetProperSubset(self.args[1], self.args[0]),
            self,
            "superset => subset").simplify(**sopts)

