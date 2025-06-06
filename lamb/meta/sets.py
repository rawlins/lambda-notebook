import random
import collections.abc
import lamb
from lamb import types, utils
from .core import derived, registry, get_type_system, BindingOp, TypedExpr, get_sopt
from .core import BinaryGenericEqExpr, SyncatOpExpr, LFun, TypedTerm, to_python_container
from .core import Tuple, is_concrete, to_concrete, TypeEnv, is_equality, tp, te
from .core import op_class, MapFun, ChainFun
from . import meta
from .meta import MetaTerm
from .ply import alphanorm_key, set_derivation
from .boolean import BinaryOrExpr, BinaryAndExpr, false_term, true_term
from .quantifiers import Forall, Exists
from lamb.utils import dbg_print
from lamb.types import type_t, SetType


def derived_classes():
    # because this is happening in a lamb.meta module, load order for these
    # is tricky; it requires a fully working parser with the precondition
    # classes for <= and <. Therefore, generate them in a call from the
    # operator setup function.
    global SetSupset, SetProperSupset

    @op_class('>=', te('L x_{X} : L y_{X} : y <= x'),
                op_name_uni='⊇',
                op_name_latex='\\supseteq{}')
    class SetSupset:
        """Binary relation of (non-proper) supersethood."""
        pass

    @op_class('>', te('L x_{X} : L y_{X} : y < x'),
                op_name_uni='⊃',
                op_name_latex='\\supset{}')
    class SetProperSupset:
        """Binary relation of proper supersethood."""
        pass


def setup_operators():
    registry.add_operator(SetContains)
    registry.add_operator(SetUnion)
    registry.add_operator(SetIntersection)
    registry.add_operator(SetDifference)
    registry.add_operator(SetEquivalence,
        shadow_warning=False)
    registry.add_operator(SetSubset)
    registry.add_operator(SetProperSubset)
    registry.add_binding_op(ConditionSet)

    registry.add_operator(FunDom)
    registry.add_operator(FunCodom)

    derived_classes()
    registry.add_operator(SetSupset)
    registry.add_operator(SetProperSupset)


def safevar(e, typ=None):
    # a set-specific set of heuristics for finding a good usable/safe variable.
    varname = "x"
    if isinstance(e, ConditionSet):
        varname = e[0].op
        typ = e.type.content_type
    elif isinstance(e, BinarySetOp) or isinstance(e, SetSupset) or isinstance(e, SetProperSupset):
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


def finite_safe(s):
    """Is it safe to assume, independent of the domain, that `s` is a finite
    set? This essentially syntactically checks if `s` is a ListedSet or if it
    is constructed from ListedSets via the set operations intersection, union,
    and difference in the appropriate way for each operation.

    Returns
    -------
    bool
        can the set be safely assumed to be finite? A return value of ``False``
        doesn't indicate non-finiteness, only that finiteness can't be
        determined syntactically."""
    if isinstance(s, ListedSet) or isinstance(s, MetaTerm):
        # XX a ListedSet of sets could still contain non-finite members
        return True
    elif isinstance(s, ConditionSet) or isinstance(s, TypedTerm):
        # XX in principle, one could easily figure out that certain
        # ConditionSets are finite...
        if is_emptyset(s):
            return True
        return False
    elif isinstance(s, SetIntersection):
        return finite_safe(s[0]) or finite_safe(s[1])
    elif isinstance(s, SetUnion):
        return finite_safe(s[0]) and finite_safe(s[1])
    elif isinstance(s, SetDifference):
        return finite_safe(s[0]) # s[1] doesn't matter
    else:
        return False # not a set?


class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""

    canonical_name = "Set"
    op_name_uni="Set"
    op_name_latex="Set"
    commutative = False # A bit meaningless, since Set x: Set y: can't occur

    def __init__(self, var, body, *, typ=None, **kwargs):
        # type constraint: self.type == SetType(var.type)
        typ, wvar = self.type_constraint(typ, SetType(var.type))
        # the type constraint may have adjusted the variable type, update it
        if var.type != wvar[0]:
            var = TypedTerm(var.op, wvar[0])

        super().__init__(var, body, body_type=types.type_t, typ=typ, **kwargs)
        # superclass may have updated vartype while reconciling with the body
        self.type = SetType(self.vartype)

    def apply_var_constraints(self):
        # allow polymorphic variables. These don't exactly work simply,
        # but we do currently use {∀X} as the type for an empty set when
        # nothing else is known...
        pass

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

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self[0], self.body)

    def _compile(self, domain=None):
        # XX the use of domain here is very ad hoc, generalize
        if is_emptyset(self):
            return lambda context: set()

        if domain is None:
            if not self.finite_safe():
                raise NotImplementedError(f"Compiled ConditionSet (`{repr(self)}`)requires a guaranteed-finite domain")
            # without the demeta step, we get potentially bad comparisons
            # XX consider adjusting the domain_iter api so that it can do this
            # directly?
            # XX what about when domain is set?
            fixed_domain = tuple(types.demeta(x) for x in self.domain_iter())
            domain = lambda context: fixed_domain
        f = self.to_characteristic()._compiled
        return lambda context: frozenset({elem for elem in domain(context) if f(context)(elem)})

    def eliminate(self, **sopts):
        # For the case where there are no free terms at all, we can convert to
        # a ListedSet via domain enumeration.
        if self.finite_safe() and not self.free_terms():
            a = self.scope_assignment()
            sopts['evaluate'] = True
            subs = [MetaTerm(elem, typ=self[0].type)
                    for elem in self.domain_iter()
                    if self[1]
                            .under_assignment(a | {self.varname : elem})
                            .simplify_all(**sopts) == true_term]
            return derived(
                sset(subs, self.type),
                self,
                f"ConditionSet => ListedSet (generic on {self.varname})")
        return self

    def simplify(self, **sopts):
        if self[1] == false_term:
            return derived(emptyset(self.type), self, "trivial set condition")
        elif (isinstance(self[1], SetContains) and self[1][0] == self[0]
                and self.varname not in self[1][1].free_terms()):
            # XX these two are annoyingly special-case-y, and are primarily
            # here because automatic simplification will generate such
            # expressions.
            # a better approach might at least do something like first go to
            # cnf, and then check all conjuncts. Or, perhaps to do some form
            # of anti-elimination so as to get set characterizations that meet
            # this criteria?
            return derived(self[1][1].copy(), self, "condition directly characterizes")
        elif is_equality(self[1]):
            target = None
            if self[1][0] == self[0]:
                target = self[1][1]
            elif self[1][1] == self[0]:
                target = self[1][0]
            if target is not None and self.varname not in target.free_terms():
                return derived(ListedSet(target.copy(), typ=self.type),
                    self,
                    "condition directly characterizes")
        elif (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self.finite_safe()):
            # XX make come apart from the general `eliminate` option?
            return self.eliminate(**sopts)

        return self


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

    def __init__(self, *elements, typ=None, assignment=None, **kwargs):
        """Construct a `ListedSet` instance. note! uniqueness is not enforced here.
        Syntactic duplicates are removed only on simplify. (However, the
        metalanguage parser will filter out duplicates in advances as part of
        parsing a set expression.)"""
        # XX is this pre-call necessary
        args = [self.ensure_typed_expr(a, assignment=assignment) for a in elements]
        if len(args) == 0:
            # could be a set of anything
            typ, _ = self.type_constraint(typ, SetType(types.VariableType.any()))
        else:
            # inherit the type from the first argument
            typ, _ = self.type_constraint(typ, SetType(args[0].type))

        inner_type = typ[0]

        def _update_types(ityp, args):
            # take a single pass through elements and apply `typ` as an element
            # constraint
            for i in range(len(args)):
                ityp, args[i] = self.type_constraint(ityp, args[i],
                    error=f"Set elements must have compatible types (`{repr(args[i])}` at type `{ityp}`)")
            return ityp

        styp = _update_types(inner_type, args)
        if styp != inner_type:
            # we strengthened, somewhere along the line. `styp` should now be
            # the strongest principal type compatible with all elements. Make
            # sure that all elements do have this type.
            _update_types(styp, args)

        super().__init__("ListedSet", *args)
        self.type = SetType(styp)
        self.set_simplified = False

    def calc_type_env(self, recalculate=False):
        if len(self) == 0:
            env = TypeEnv()
            env.add_type_to_var_set(self.type)
            return env
        else:
            # otherwise, rely on the contained elements
            return super().calc_type_env(recalculate=recalculate)

    def copy_local(self, *args, typ=None, **kwargs):
        # explicit handling of empty sets in order to get the type right
        if len(args) == 0 and typ is None:
            # don't allow any types weaker than self.type to be inferred for
            # an empty set
            typ = self.type

        return self.copy_core(ListedSet(*args, typ=typ))

    @classmethod
    def join(self, l):
        # the constructor already matches the `join` api, and this is just for
        # completeness. It ensures presimplification.
        return sset(l)

    def term(self):
        return False

    def name_of(self, i):
        return f"element {i}"

    def _compile(self):
        # XX could optimize further if self is purely meta...
        l = [a._compiled for a in self.set()]
        return lambda context: frozenset(elem(context) for elem in l)

    def set(self):
        """Return a python `frozenset` of elements in the ListedSet. This of
        course uses syntactic identity, so while every term will be unique via
        this criteria, it is not guaranteed to be the "true" set (unless it
        consists only of `MetaTerm`s)."""
        return frozenset(self.args)

    def sorted_set(self):
        s = self.set()
        return sorted(s, key=alphanorm_key)

    def to_condition_set(self):
        """Convert to a condition set by disjoining members."""
        s = self.simplify()
        # XX should this use << instead? then simplification to disjunction
        # is more controllable, and this function would be simpler
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
        # XX could this more drastically normalize via to_concrete?
        args = set(self.args) # remove duplicates, flatten order
        domain = self.type.content_type.domain
        # assumption: there is no truly empty domain, so if domain.domain is
        # empty, it is not actually in use.
        if domain.finite and domain.domain and args > domain.domain:
            # if every domain element is present in `args`, drop extraneous
            # elements. E.g. `{True, False, p_t}` simplifies to just {True, False}.
            # sadly, we can't rely on & here; since domain elements are not
            # MetaTerms, it can result in non-MetaTerms in args.
            args = {a for a in args if a in domain.domain}
        args = sorted(args, key=alphanorm_key) # for a canonical ordering
        result = self.copy_local(*args)
        result.set_simplified = True
        set_derivation(result, self.derivation) # copy any derivation, no changes
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

    @classmethod
    def random(self, ctrl, max_type_depth=1, max_members=6, typ=None, allow_empty=True):
        if typ is None:
            typ = SetType(get_type_system().random_type(max_type_depth, 0.5))
        if allow_empty:
            r = range(max_members+1)
        else:
            r = range(max_members+1)[1:]
        length = random.choice(r)
        members = [ctrl(typ=typ[0]) for i in range(length)]
        if not length and random.choice([True, False]):
            # untyped (`{?}`) empty set
            return sset(members)
        else:
            return sset(members, settype=typ)


def sset(iterable, settype=None, innertype=None, assignment=None):
    # factory that calls do_simplify
    if innertype is None:
        if settype is not None and not isinstance(settype, SetType):
            raise ValueError("Set construction by set type requires a SetType!")
    else:
        if settype is not None:
            raise ValueError("Set construction requires either a content type or a set type, not both!")
        settype = SetType(innertype)
    return ListedSet(*list(iterable), typ=settype, assignment=assignment).do_simplify()


def emptyset(settype=None, **kwargs):
    """Convenience factory for empty sets"""

    return sset(set(), settype=settype, **kwargs)


def is_emptyset(s):
    """Syntactic emptyset check. False for a ConditionSet doesn't mean that it
    isn't the emptyset, just that that can't be determined syntactically."""
    return (isinstance(s, ListedSet) and len(s) == 0
        or isinstance(s, ConditionSet) and s[1] == false_term
        or isinstance(s, MetaTerm) and isinstance(s.type, SetType) and len(s.op) == 0
        or isinstance(s, collections.abc.Set) and len(s) == 0)


def is_domainset(s):
    """Is `s` a TypedExpr that (syntactically) corresponds to the set of all
    elements in some type domain? (aka `Set x_X : True` for some type X)"""
    # XX could check finite domains for listed cases as well?
    return isinstance(s, ConditionSet) and s[1] == true_term


def is_trivial_set(s):
    return is_emptyset(s) or is_domainset(s)


def is_trivial_set_op(s):
    # convenience function for simplificiation. Checks one level of recursion
    return any(is_trivial_set(sub) for sub in s)


class SetContains(SyncatOpExpr):
    """Binary relation of set membership.  This uses `<<` as the symbol.

    Note that this _does_ support reduction if the set describes its members by
    condition, as set membership is equivalent to saturation of the
    characteristic function of the set."""

    arity = 2
    canonical_name = "<<"
    op_name_uni = "∈"
    op_name_latex = "\\in{}"
    commutative = False

    arg_signature = tp("(X,{X})")

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)

        arg2, settype = self.type_constraint(arg2, SetType(arg1.type),
            error="Right operand of `<<` must be a set type matching left operand")
        # now resolve any type inference that may impact back on arg1
        arg1 = self.type_constraint(arg1, settype[0], constant=True,
            error="Right operand of `<<` must be a set type matching left operand")

        super().__init__(typ, arg1, arg2, tcheck_args=False)

    def _compile(self):
        arg = self[0]._compiled
        if isinstance(self[1], ConditionSet):
            # short-circuit the finiteness requirement if we were to directly
            # compile self[1]
            fun = self[1].to_characteristic()._compiled
            return lambda context: fun(context)(arg(context))
        else:
            # XX can any of these cases be further optimized? Probably at least
            # ListedSet?
            s = self[1]._compiled
            return lambda context: arg(context) in s(context)

    def simplify(self, **sopts):
        elem_concrete = is_concrete(self[0])
        set_concrete = is_concrete(self[1])
        if set_concrete and elem_concrete:
            # this case is fully executable
            return derived(MetaTerm(meta.exec(self)), self, "∈ simplification")
        elif isinstance(self[1], ListedSet) or set_concrete:
            s = to_concrete(self[1])
            if len(s) == 0:
                return derived(false_term, self, "∈ simplification (empty set)")

            e = to_concrete(self[0])
            if e in s:
                # positive membership is safe. (Negative membership isn't...)
                return derived(MetaTerm(true_term), self, "∈ simplification")
            elif len(s) == 1:
                # this case is almost always better to convert to an <=>
                # expression
                content, = s
                return derived(e.equivalent_to(content), self,
                                            "∈ simplification (singleton set)")
            elif get_sopt('eliminate_sets_all', sopts):
                # in the general case we can convert to a disjunction of <=>
                # expressions. However, this tends to produce fairly long
                # expressions that are slow to evaluate; in cases where there's
                # a better simplification algorithm, in my testing, the penalty
                # for doing this conversion can be something like 1 order of
                # magnitude if the set is even moderately sized
                # (e.g. 200ms=>2s). We therefore only do this with an explicit
                # option.
                # XX maybe could do this for small sets unconditionally?
                # XX this might be a reasonable case to actually check the
                # complexity of the resulting expression. Example:
                # `_c2 << {_c1, x_e}` results in eliminating _c1 from the
                # picture. This is special cased below, but we could eliminate
                # the case, maybe?
                conditions = [(self[0] % a) for a in self[1]]
                return derived(BinaryOrExpr.join(conditions),
                    self,
                    "∈ simplification (∈ to ∨ elimination)").simplify_all(**sopts)
            elif elem_concrete:
                # we should have a non-concrete ListedSet, and a concrete
                # element. For this case, we can filter any non-matching
                # concrete elements from the set. We know because of the
                # order of ifs that no concrete elements match.
                # (N.b. this is actually handled well by simplification paths
                # under eliminate_sets_all! But the general case of that is
                # much worse, so we special case things here if that option
                # is not set.)
                news = frozenset(elem for elem in s if not is_concrete(elem))
                if news != s:
                    # rerun simplify, essentially for the sake of only the
                    # singleton case above. (XX can the elif order be adjusted
                    # to get this directly, with derivational history?)
                    return derived(SetContains(self[0], sset(news, self[1].type)),
                        self,
                        "∈ simplification (concrete filtering)").simplify(**sopts)
        elif isinstance(self[1], ConditionSet):
            derivation = self.derivation
            # XX should this be reduce_all?
            step = (self[1].to_characteristic()(self[0])).reduce()
            set_derivation(step, derivation) # suppress the intermediate parts of
                                             # this derivation, if any
            return derived(step, self, "∈ simplification")

        # leave other ListedSets as-is for now.
        return self

    @classmethod
    def random(cls, ctrl, max_type_depth=1, typ=None):
        if typ is None:
            typ = get_type_system().random_type(max_type_depth, 0.5)
        return SetContains(ctrl(typ=typ), ctrl(typ=SetType(typ)))


def check_set_types(arg1, arg2, op_name=None):
    if isinstance(arg1.type, SetType):
        primary = arg1
        other = arg2
    elif isinstance(arg2.type, SetType):
        primary = arg2
        other = arg1
    # XX missing case: both types are type variables
    # this is mostly shadowed by other operators, but perhaps in a buggy way.
    # E.g. `%te p_Y <= q_X` resolves to type n, but should arguably give an
    # ambiguous operator parse error. <=> is more intentionally shadowed by
    # BinaryGenericEqExpr...
    else:
        if op_name:
            # XX these errors are a bit odd
            raise types.TypeMismatch(arg1, arg2, error=f"{op_name} requires set types")
        else:
            return None

    if types.is_type_var(other.type):
        return primary.type
    elif not isinstance(other.type, SetType):
        if op_name:
            # XX these errors are a bit odd
            raise types.TypeMismatch(arg1, arg2, error=f"{op_name} requires set-compatible types")
        else:
            return None
    # at this point, both are SetType instances
    ctype = get_type_system().unify(arg1.type.content_type, arg2.type.content_type)
    if ctype is None:
        if op_name:
            raise types.TypeMismatch(arg1, arg2, error=f"{op_name} requires equivalent set types")
        else:
            return None

    return SetType(ctype)


# note: classes in derived_classes() do not subclass, so an isinstance check
# on this is not guaranteed to get every operator!
class BinarySetOp(SyncatOpExpr):
    arity = 2
    arg_signature = tp("({X},{X})")

    def __init__(self, arg1, arg2, op_name, rettype=None, typ=None):
        t = check_set_types(arg1, arg2, op_name=op_name)
        if rettype is None:
            # treat `t` also as the return type
            t, _ = self.type_constraint(t, typ)
            rettype = t
        else:
            self.type_constraint(typ, rettype, constant=True)

        arg1 = self.type_constraint(arg1, t, constant=True)
        arg2 = self.type_constraint(arg2, t, constant=True)
        super().__init__(t, arg1, arg2, typ=rettype, tcheck_args=False)

    def _compile(self):
        impl = self._set_impl()
        if impl is None:
            raise NotImplementedError
        impl = impl._compiled
        return lambda context: impl(context)

    def _set_impl(self):
        # set operations and relations typically have an implementation in terms
        # of simpler operations/relations; subclasses can fill this in here.
        return None

    @classmethod
    def random(cls, ctrl, max_type_depth=1, typ=None):
        if cls == BinarySetOp:
            raise NotImplementedError("`random` called on abstract class `BinarySetOp`")
        if typ is None:
            typ = SetType(get_type_system().random_type(max_type_depth, 0.5))
        # XX random ConditionSet
        return cls(ctrl(typ=typ), ctrl(typ=typ))


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

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Set union", typ=typ)

    def _set_impl(self):
        var = safevar(self)
        return ConditionSet(var, var << self[0] | var << self[1])

    def _compile(self):
        if finite_safe(self):
            s1 = self[0]._compiled
            s2 = self[1]._compiled
            return lambda context: s1(context) | s2(context)
        else:
            return super()._compile()

    def simplify(self, **sopts):
        s1 = to_python_container(self[0])
        s2 = to_python_container(self[1])
        if s1 is not None and s2 is not None:
            if is_concrete(self[0]) and is_concrete(self[1]):
                result = s1 | s2
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                if self[0].meta() and self[1].meta():
                    result = MetaTerm(result, typ=self.type)
                else:
                    result = sset(result, self.type)
                return derived(result, self, "set union")
            else:
                # this is code dup to above, but it is conceptually helpful to
                # single out this case. ListedSet union is pleasantly simple
                # compared to other operations. We can safely take the union
                # even with unresolved terms.
                return derived(sset(s1 | s2, self.type), self, "set union")
        elif s1 is not None and len(s1) == 0:
            return derived(self[1], self, "set union") # {} | X = X
        elif s2 is not None and len(s2) == 0:
            return derived(self[0], self, "set union") # X | {} = X

        # for everything except ConditionSets, this tends to make the formula
        # more unwieldy
        if (isinstance(self[0], ConditionSet) and isinstance(self[1], ConditionSet)
                or is_trivial_set_op(self)
                or get_sopt('eliminate_sets', sopts)):
            return derived(self._set_impl(), self,
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

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Set intersection", typ=typ)

    def _set_impl(self):
        var = safevar(self)
        return ConditionSet(var, var << self[0] & var << self[1])

    def _compile(self):
        if finite_safe(self[0]) and finite_safe(self[1]):
            s0 = self[0]._compiled
            s1 = self[1]._compiled
            return lambda context: s0(context) & s1(context)
        elif finite_safe(self):
            # XX code dup
            # this is pretty messy as-is
            if finite_safe(self[0]):
                domain = self[0]._compiled
            else:
                domain = self[1]._compiled
            return self._set_impl()._compile(domain=domain)
        else:
            return super()._compile()

    def simplify(self, **sopts):
        s1 = to_python_container(self[0])
        s2 = to_python_container(self[1])
        if s1 is not None and s2 is not None:
            if is_concrete(self[0]) and is_concrete(self[1]):
                result = s1 & s2
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                if self[0].meta() and self[1].meta():
                    result = MetaTerm(result, typ=self.type)
                else:
                    result = sset(result, self.type)
                return derived(result, self, "set intersection")

            if s1 <= s2 or s2 <= s1:
                # this case is also also safe: there's no way for expression
                # resolution to expand sets that are in a subset relation.
                return derived(
                    sset(s1 & s2, self.type),
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

            definite_expr = sset(definite, self.type)

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
                    ConditionSet(var, (var << self[0]) & (var << self[1])),
                    self,
                    "set intersection (set elimination)")

            tbd = ConditionSet(var, (var << sset(tbd, self.type)
                                        & (var << sset(s1 - definite, self.type))
                                        & (var << sset(s2 - definite, self.type))))
            return derived((definite_expr | tbd), self, "set intersection (set elimination)").simplify_all(**sopts)

        elif s1 is not None and len(s1) == 0:
            return derived(emptyset(self.type), self, "set intersection") # {} & X = {}
        elif s2 is not None and len(s2) == 0:
            return derived(emptyset(self.type), self, "set intersection") # X & {} = {}

        if (isinstance(self[0], ConditionSet) and isinstance(self[1], ConditionSet)
                or is_trivial_set_op(self)
                or get_sopt('eliminate_sets', sopts)):
            return derived(self._set_impl(), self,
                "set intersection (set elimination)").simplify_all(**sopts)
        return self


class SetDifference(BinarySetOp):
    """Binary operation of set difference."""

    canonical_name = "-"
    op_name_latex = "-"
    commutative = False
    associative = False
    pre_simplify = True

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Set difference", typ=typ)

    def _set_impl(self):
        var = safevar(self)
        return ConditionSet(var, var << self[0] & (~(var << self[1])))

    def _compile(self):
        if finite_safe(self):
            # it's safe to work with the left argument directly
            s1 = self[0]._compiled
            if finite_safe(self[1]):
                s2 = self[1]._compiled
                return lambda context: s1(context) - s2(context)
            else:
                var = safevar(self)
                # XX code dup
                impl = LFun(var, (var << self[1]))._compiled
                return lambda context: frozenset({e for e in s1(context) if not impl(context)(e)})
        elif is_domainset(self[1]):
            # even if left isn't finite-safe, if we have the domain set on the
            # right, we can know that the result is the empty set.
            # very special case-y, but simplify handles this. Can this be
            # generalized somehow? This is basically "if the right condition
            # entails the left" at the strongest special case of that.
            return lambda context: set()
        else:
            return super()._compile()

    def simplify(self, **sopts):
        left = self[0]
        right = self[1]
        if is_emptyset(left):
            return derived(emptyset(self.type), self, "set difference") # {} - X = {}
        elif is_emptyset(right):
            return derived(left, self, "set difference") # X - {} = X

        s1 = to_python_container(left)
        s2 = to_python_container(right)
        if s1 is not None and s2 is not None:
            # there are various special cases of two listed sets that can be
            # handled
            left_is_concrete = is_concrete(left)
            if left_is_concrete and is_concrete(right):
                # the easy case -- we can just do subtraction sanely
                result = s1 - s2
                # only generate a metaterm if we started with two metaterms,
                # independent of the content
                if left.meta() and left.meta():
                    result = MetaTerm(result, typ=self.type)
                else:
                    result = sset(result, self.type)
                return derived(result, self, "set difference")

            if s2 == s1:
                # syntactic identity guarantees the empty set
                return derived(emptyset(self.type), self, "set difference")

            right_concrete = {e for e in s2 if is_concrete(e)}
            if right_concrete and right_concrete & s1:
                # we can safely eliminate these elements on the left. Note that
                # we *can't* generally eliminate them on the right. Example:
                # `{_c1, x_e} - {_c1}`. `x` could be `_c1`, so generating
                # `{x_e} - {}` is potentially wrong!
                # when the left set is fully concrete, this is safe
                left = sset(s1 - right_concrete, self.type)
                if left_is_concrete:
                    right = sset(s2 - right_concrete, self.type)
                # generate the filtered set, and recurse once (in case eliminate_sets
                # should also be applied)
                return derived(left - right, self, "set difference").simplify(**sopts)
            # XX implement something more here?
            # warning: cases like {X,Y} - {Y} are not safe to simplify under
            # syntactic identity, since if X == Y, then {X} is actually wrong.
        elif s2 is not None and isinstance(left, ConditionSet):
            # XX is this too much to do unconditionally? For toy domains it's
            # fine, good even, but this could produce very large results.
            left_elim = left.eliminate()
            if left_elim is not left:
                return derived(left_elim - right, self, "set difference (finite domain)").simplify(**sopts)

        if (isinstance(self[0], ConditionSet) and isinstance(self[1], ConditionSet)
                or is_trivial_set_op(self)
                or get_sopt('eliminate_sets', sopts)):
            return derived(self._set_impl(), self,
                "set difference (set elimination)")#.simplify_all(**sopts)
        return self


class SetEquivalence(BinarySetOp):
    """Binary relation of set equivalence."""

    canonical_name = "<=>"
    secondary_names = {"==", "%"}
    op_name_latex = "="
    commutative = True

    arg_signature = tp("({X},{X})")

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Set equivalence", rettype=types.type_t, typ=typ)

    def _set_impl(self):
        # this is general, but unfortunately kind of bad in a lot of special
        # cases
        var = safevar(self)
        return Forall(var, ((var << self[0]).equivalent_to(var << self[1])))

    def _compile(self):
        # don't use the default implementation for compilation; among other
        # reasons is that it won't handle ListedSets very well.

        # Caveat: For equivalence, there are cases that only static analysis can
        # deal with.
        # The prime target here is identity laws involving {Set x: True}; meta
        # sets cannot represent this in any way so it becomes difficult to
        # reason over in compiled form. There are special cases where we could
        # just work with the conditions, but that doesn't generalize. For
        # example:
        #   ((Set x_e: True_t) <=> ((Set x_e: True_t) & (Set x_e: False_t)))
        # (i.e. the implementation of <=).
        #
        # n.b. this point generalizes in a tricky way, though equivalence is
        # a scenario where this comes up. So for example, while
        #     `((Set x_e: True) & (Set x_e: False)) & {_c1, _c2}`
        # will compile,
        #     `((Set x_e: True) & (Set x_e: True)) & {_c1, _c2}`
        # won't.

        if is_trivial_set(self[0]) and is_trivial_set(self[1]):
            # XX this could be more general; if either or both is a vacuous
            # condition set, we could run it and compare
            # note: this won't work right if an empty domain is possible...
            result = is_emptyset(self[0]) == is_emptyset(self[1])
            return lambda context: result
        elif self[0] == self[1]:
            # Special case syntactic positive identity. Code dup with generic eq
            return lambda context: True

        # if l and/or r are ConditionSets, compiling will require finiteness at
        # this point.
        l = self[0]._compiled
        r = self[1]._compiled
        # XX there are definitely some optimizations from simplify that would
        # be worth importing here. And using python equality is kind of bug-prone.
        # to what degree can the finiteness constraint be eliminated?
        return lambda context: l(context) == r(context)

    def simplify(self, **sopts):
        s1 = to_python_container(self[0])
        s2 = to_python_container(self[1])
        if s1 is not None and s2 is not None:
            if len(s1) == 0 or len(s2) == 0:
                # this case is relatively straightforward: we can go simply
                # on the basis of expression cardinality
                return derived(MetaTerm(len(s1) == len(s2)),
                                                    self, "set equivalence (empty set)")
            elif is_concrete(self[0]) and is_concrete(self[1]):
                # an alternative would be to use `to_concrete` to convert this
                # to a normalized form and then compare, but we might as well
                # just execute
                return derived(MetaTerm(meta.exec(self)), self, "set equivalence")
            elif len(s1) == len(s2) and s1 == s2:
                # special case syntactic equality, this one is safe for just
                # the positive check. The cardinality check is a much simpler
                # precondition to know if we should bother invoking whatever
                # == does.
                return derived(true_term, self, "set equivalence (identical)")
            elif len(s1) == 1 and len(s2) == 1:
                # special case two singletons. This isn't necessarily simple
                # depending on what they are, but for many cases it can be.
                e1, = s1
                e2, = s2
                return derived(e1.equivalent_to(e2),
                                self, "set equivalence (singleton sets)").simplify_all(**sopts)

            # normalize any concrete parts. At this point, neither of these
            # can be fully concrete.
            s1 = to_concrete(s1)
            s2 = to_concrete(s2)

            # tally up all the potential mismatches
            # example: {_c1, _c2, x_e, y_e} <=> {_c2, _c3, y_e, z_e, a_e}
            # these sets could be equivalent, under certain circumstances.
            # meta_left: {_c1}, meta_right: {_c3}
            # tbd_left: {x_e}, tbd_right: {z_e, a_e}
            # The sets are equivalent if x or y = _c3, and one of y, z or a = _c1,
            # and z or a don't introduce any new elements.
            # generally, if all the tbd_left elements cover all the meta_right
            # elements and same for tbd_right vs meta_left -- no leftovers.
            # From this example you can see that clear positive overlaps can't
            # even be ignored, because variable resolution leaves everything
            # quite tbd.
            meta_left = {x for x in s1 - s2 if is_concrete(x)} # meta elements present only on the left
            tbd_left = s1 - s2 - meta_left # non-meta elements present on the left
            meta_right = {x for x in s2 - s1 if is_concrete(x)} # meta elements present only on the right
            tbd_right = s2 - s1 - meta_right # non-meta elements present on the right

            if len(tbd_left) == 0 and len(tbd_right) == 0:
                # only MetaTerms
                return derived(MetaTerm(len(meta_left) == 0 and len(meta_right) == 0),
                                self, "set equivalence")
            # there's more fine-grained checks that could be done for mixed
            # meta/non-meta sets. For one thing, this code is acting as if
            # all we're dealing with in the tbds are terms, and that is
            # certainly a main case, but it's far from exhaustive.
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
                    Forall(var, ((var << self[0]).equivalent_to(
                            var << sset(s2 - s1, self[0].type)))),
                    self,
                    "set equivalence (set elimination)").simplify_all(**sopts)
            elif s2 < s1:
                return derived(
                    Forall(var, ((var << self[1]).equivalent_to(
                            var << sset(s1 - s2, self[0].type)))),
                    self,
                    "set equivalence (set elimination)").simplify_all(**sopts)

            # at this point, fallthrough to the general case. (Is there anything
            # better that could be done?)

        if (isinstance(self[0], ConditionSet) and isinstance(self[1], ConditionSet)
                or is_trivial_set_op(self)
                or get_sopt('eliminate_sets', sopts)):
            return derived(self._set_impl(), self,
                "set equivalence (set elimination)").simplify_all(**sopts)
        return self

# the remaining set relations for implementation primarily rely on the above
# operations plus equivalence checking. Cases handled there will follow
# directly from the _set_impl code below without too much pain; this especially
# includes concrete sets and all compiled sets.
#
# However, all of the simplify implementations check whether simplifying the
# _set_impl return does something, and this is a bit flawed in many cases,
# since there may be fairly trivial tweaks in combination with formula
# explosion that pass. (TODO)

class SetSubset(BinarySetOp):
    """Binary relation of (non-proper) subsethood."""

    canonical_name = "<="
    op_name_uni = "⊆"
    op_name_latex = "\\subseteq{}"
    commutative = False

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Subset", rettype=types.type_t, typ=typ)

    def _set_impl(self):
        return self[0].equivalent_to(self[0] & self[1])

    def simplify(self, **sopts):
        old_derivation = self.derivation
        test = derived(self._set_impl(), self, "subset (set elimination)")
        simplified = test.simplify_all(**sopts)
        if simplified is test and not get_sopt('eliminate_sets', sopts):
            # if simplify didn't do anything to this expression, the result is
            # probably not actually simpler than where we started
            set_derivation(self, old_derivation)
            return self
        else:
            return simplified


class SetProperSubset(BinarySetOp):
    """Binary relation of proper subsethood."""

    canonical_name = "<"
    op_name_uni = "⊂"
    op_name_latex = "\\subset{}"
    commutative = False

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        super().__init__(arg1, arg2, "Proper subset", rettype=types.type_t, typ=typ)

    def _set_impl(self):
        return ((self[0] <= self[1]) & (~(self[0].equivalent_to(self[1]))))

    def simplify(self, **sopts):
        old_derivation = self.derivation
        test = derived(self._set_impl(), self, "proper subset (set elimination)")
        simplified = test.simplify_all(**sopts)
        if simplified is test and not get_sopt('eliminate_sets', sopts):
            set_derivation(self, old_derivation)
            return self
        else:
            return simplified


class FunDom(TypedExpr):
    canonical_name = "Dom"
    pre_simplify = True

    arg_signature = tp("(<X,Y>,)")

    def __init__(self, arg, typ=None, **kwargs):
        arg = self.type_constraint(arg, types.FunType)
        typ, _ = self.type_constraint(SetType(arg.type[0]), typ)
        super().__init__("Dom", arg, typ=typ)

    def _find_domain(self, cur):
        # XX MetaTerm implementation details shouldn't be here
        if (isinstance(cur, LFun)
                    or (isinstance(cur, MetaTerm)
                        and isinstance(cur.op, collections.abc.Set))):
            # XX how should this condition interact with Partial?
            return ConditionSet(TypedTerm('x', typ=cur.type[0]), true_term)
        elif isinstance(cur, MapFun):
            return sset(cur.arg_map.keys())
        elif (isinstance(cur, MetaTerm)
                    and isinstance(cur.op, collections.abc.Mapping)):
            return sset(cur.dict().keys())
        elif isinstance(cur, ChainFun):
            return self._find_domain(cur[0]) | self._find_domain(cur[1])
        else:
            # unvalued terms, MetaTerm with a python function implementation, Partial, ...
            if cur is self:
                return self
            else:
                return FunDom(cur)

    def _compile(self):
        if self[0].term():
            f_term = self[0]._compiled
            # we need to compile this on spec. This will raise if we aren't
            # working with a finite domain for the type at time of compilation.
            max_domain = ConditionSet(TypedTerm('x', typ=cur.type[0]), true_term)._compiled
            def term_inner(context):
                f = f_term(context)
                if isinstance(f, collections.abc.Mapping):
                    return frozenset(f.keys())
                elif isinstance(f, collections.abc.Set):
                    return max_domain(context)
                else:
                    # if this term is backed by a python function, it's not
                    # possible to get the domain set. Unfortunately we can't
                    # detect this until runtime...
                    raise NotImplementedError
            return term_inner
        else:
            # XX this won't handle complex domains involving terms...
            dom = self._find_domain(self[0])
            if dom is self:
                raise NotImplementedError
            return dom._compiled

    def simplify(self, **sopts):
        result = self._find_domain(self[0])
        if result is not self:
            result = derived(result, self, "Function domain simplification")
        return result


class FunCodom(TypedExpr):
    canonical_name = "Codom"
    pre_simplify = True

    arg_signature = tp("(<X,Y>,)")

    def __init__(self, arg, typ=None, **kwargs):
        arg = self.type_constraint(arg, types.FunType)
        typ, _ = self.type_constraint(SetType(arg.type[1]), typ)
        super().__init__("Codom", arg, typ=typ)

    def _find_codomain(self, cur):
        # XX MetaTerm implementation details shouldn't be here
        if (isinstance(cur, LFun)
                    or (isinstance(cur, MetaTerm)
                        and isinstance(cur.op, collections.abc.Set))):
            # the char function case could be streamlined
            return ConditionSet(TypedTerm('x', typ=cur.type[1]), true_term)
        elif isinstance(cur, MapFun):
            return sset(cur.arg_map.values())
        elif (isinstance(cur, MetaTerm)
                    and isinstance(cur.op, collections.abc.Mapping)):
            return sset(cur.dict().values())
        elif isinstance(cur, ChainFun):
            return self._find_codomain(cur[0]) | self._find_codomain(cur[1])
        else:
            # unvalued terms, MetaTerm with a python function implementation, Partial, ...
            return self

    def _compile(self):
        if self[0].term():
            f_term = self[0]._compiled
            # we need to compile this on spec. This will raise if we aren't
            # working with a finite domain for the type at time of compilation.
            max_range = ConditionSet(TypedTerm('x', typ=cur.type[1]), true_term)._compiled
            def term_inner(context):
                f = f_term(context)
                if isinstance(f, collections.abc.Mapping):
                    return frozenset(f.keys())
                elif isinstance(f, collections.abc.Set):
                    return max_range(context)
                else:
                    # if this term is backed by a python function, it's not
                    # possible to get the domain set. Unfortunately we can't
                    # detect this until runtime...
                    raise NotImplementedError
            return term_inner
        else:
            # XX this won't handle complex domains involving terms...
            codom = self._find_codomain(self[0])
            if codom is self:
                raise NotImplementedError
            return codom._compiled

    def simplify(self, **sopts):
        result = self._find_codomain(self[0])
        if result is not self:
            result = derived(result, self, "Function codomain simplification")
        return result

