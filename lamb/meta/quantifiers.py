import random

import lamb
from lamb import types, utils
from .core import op, derived, TypedExpr, TypedTerm, SyncatOpExpr
from .core import BindingOp, Partial, LFun, get_sopt, ts_unify, is_concrete, te
from .core import ts_reconcile
from . import meta, ply, boolean
from .boolean import true_term, false_term
from lamb.types import type_t
from lamb.utils import dbg_print


def setup_operators(language):
    language.registry.add_binding_op(Forall)
    language.registry.add_binding_op(Exists)
    language.registry.add_binding_op(ExistsExact)
    language.registry.add_binding_op(Iota)
    language.registry.add_binding_op(IotaPartial)


def deriv_generic(instantiated, generic, varname):
    if instantiated.derivation:
        # copy the last step of `instantiated`'s derivation into generic,
        # without any other history from `instantiated`. (Is this general
        # enough?)
        # this will truncate a lot of derivation. But it's hard to see a way
        # around this. Simple example: Forall p_t : Exists q_t : p == q
        # * intuitively, might want to show something like `p == q` at the
        #   step evaluating the existential
        # * but, the verifier for the existential varies with the value of p, so
        #   there isn't easy access to a subexpression to show there
        # * but, in practice, because there's a simplify_all call, something
        #   completely different happens anyways: <=> simplifies first,
        #   leaving `Exists q_t : q` or `Exists q_t: ~q_t` depending on the
        #   value of `p`, and these make even less sense to show in isolation!
        # * one idea might be to lazily evaluate the assignment somehow?
        # * in principle, could just track every instantiation...
        i_step = instantiated.derivation[-1].copy()
        i_result = instantiated.derivation[-1].result
        i_result.derivation = None
        # XX does this always make sense?
        i_step.desc = f"{i_step.desc} (generic on {varname})"
        return derived(i_result, generic,
            desc=i_step.desc,
            # weird results from this, due to issues described above
            # subexpression=i_step.subexpression
            )
    else:
        return generic


class RestrictedBindingOp(BindingOp):
    allow_restrictor = True

    # similar to superclass: typ is required but may be None; it is *not*
    # validated in any way
    def __init__(self, var, body, /,
                restrictor, typ, *,
                body_type=None, copying=False,
                **kwargs):

        # type constraint: restrictor's type is SetType of variable's type
        if not copying and restrictor is not None:
            restrictor, rtype = self.type_constraint(restrictor, types.SetType(var.type),
                error=f"Failed to reconcile restrictor and variable type for operator class `{self.canonical_name}`")
            if rtype[0] != var.type:
                var = TypedTerm(var.op, rtype[0])

        super().__init__(var, body, typ,
                        body_type=body_type, copying=copying, **kwargs)
        if not copying and restrictor is not None and self.vartype != restrictor.type[0]:
            # inference on the variable led to another update, and the restrictor
            # needs to be brought in sync again. The variable should be strictly
            # stronger at this point, so can no longer change.
            # test case: te("Exists x_X << {y_X} : P_<e,t>(x)", let=False)
            restrictor = self.type_constraint(
                restrictor, types.SetType(self.vartype),
                constant=True,
                error=f"Failed to reconcile restrictor and variable type for operator class `{self.canonical_name}`")

        if restrictor is not None:
            self.args.extend([restrictor])
        self._reduced_cache = [None] * len(self.args)

    @property
    def restrictor(self):
        if len(self.args) == 3:
            return self.args[2]
        else:
            return None

    def restricted(self):
        from .sets import is_domainset
        return self.restrictor is not None and not is_domainset(self.restrictor)

    def get_domain(self):
        # this does not return particularly uniform objects!
        if self.restricted():
            return self.restrictor
        else:
            return self[0].type.domain

    def finite_safe(self):
        from .sets import is_emptyset, ListedSet
        if not self.restricted():
            if not self[0].type.domain.enumerable() and self[0].type.domain.finite:
                # This case should really count as True, but we are
                # currently conflating finite_safe with having a working
                # iterator. No cases currently hit this. XX separate?
                return None
            return self[0].type.domain.finite
        elif (is_emptyset(self.restrictor)
                or is_concrete(self.restrictor)
                or isinstance(self.restrictor, ListedSet)):
            return True
        else:
            return None

    def domain_iter(self):
        from .sets import is_emptyset, ListedSet
        if not self.restricted():
            return self.type_domain_iter()
        elif is_emptyset(self.restrictor):
            return iter([])
        elif self.restrictor.meta() or isinstance(self.restrictor, ListedSet):
            # XX this does not validate against current domain restrictions!
            return iter(self.restrictor.set())
        else:
            # could return a potentially non-stopping iter from restrictor?
            return None

    def empty_domain(self):
        from .sets import is_domainset
        safe = self.finite_safe()
        if safe == True:
            # we check by actually iterating. Domain sets can be quite large;
            # while they should not need to instantiate to calculate size,
            # this is a case where we can very easily assume nothing. (In
            # principle this technique could be generalize a bit; see
            # https://github.com/wbolster/cardinality/blob/master/cardinality.py)
            try:
                next(self.domain_iter())
            except StopIteration:
                return True
            return False
        elif safe == False:
            # guaranteed non-finite domain
            return False
        else:
            # ConditionSet with non-trivial condition, set variable, or
            # non-enumerable domain; can't be determined without evaluation
            return None

    def domain_cardinality(self):
        from .sets import ListedSet
        if not self.restricted():
            # generally pretty safe -- DomainSet subclasses calculate their
            # finite sizes analytically
            return super().domain_cardinality()
        elif self.empty_domain():
            # should handle all varieties of empty set
            return 0
        elif self.finite_safe():
            if is_concrete(self.restrictor):
                return len(self.restrictor.set())
            elif isinstance(self.restrictor, ListedSet) and len(self.restrictor) == 1:
                # special case: an arbitrary ListedSet of size 1 is guaranteed
                # cardinality 1. (Beyond that, we can't determine exact
                # cardinality without evaluation.)
                return 1
        # restricted but with a non-finite-safe-restriction
        return None

    def calc_type_env(self, recalculate=False):
        env = super().calc_type_env(recalculate=recalculate)
        if self.restrictor is not None:
            # note: instances of the bound variable are free in restrictor
            env.merge(self.restrictor.get_type_env())
        return env

    def latex_op_str_short(self):
        prefix = f"{self.op_name_latex} {self.varname}_{{{self.vartype.latex_str()}}}"
        coda = "\\: . \\:"
        if self.restricted():
            return f"{prefix} \\in {{\\small {self.restrictor.latex_str()}}} {coda}"
        else:
            return f"{prefix} {coda}"

    def __repr__(self):
        header = f"{self.op_name} {repr(self.var_instance)}"
        if self.restrictor is not None:
            header += f" << {repr(self.restrictor)}"
        return f"({header}: {repr(self.body)})"

    @classmethod
    def join(cls, args, empty=None):
        # `empty` is ignored
        if len(args) == 0:
            raise ValueError(f"Need at least 1 argument for BindingOp.join (got `{repr(args)}`)")
        if len(args) == 1:
            return args[0]

        start = -1
        # if the last arg is a set type, use it as a restrictor for all collected expressions.
        # this is not fully general -- if body can have SetType, then this will behave badly
        # with unary operators. However, the only binding op of which this is currently true
        # is LFun, which is unary.
        if isinstance(args[start].type, types.SetType):
            restrictor = args[start]
            start -= 1
        else:
            restrictor = None
        cur = args[start]
        for i in range(len(args) + start, 0, -1):
            if restrictor is None:
                # allow subclasses to not use `restrictor`
                cur = cls(args[i - 1], cur)
            else:
                cur = cls(args[i - 1], cur, restrictor=restrictor)

        return cur

    @classmethod
    def random(cls, ctrl, body_type=type_t, max_type_depth=1):
        base = super().random(ctrl,
                            body_type=body_type, max_type_depth=max_type_depth)
        from .sets import ListedSet
        if random.randint(0,1):
            restrictor = ListedSet.random(ctrl, max_type_depth=max_type_depth,
                typ=types.SetType(base.vartype))
            return base.copy_local(base.var_instance, base.body, restrictor)
        else:
            return base


class Forall(RestrictedBindingOp):
    """Universal binary quantifier"""
    canonical_name = "Forall"
    op_name_uni = "∀"
    op_name_latex = "\\forall{}"

    def __init__(self, var, body, /, restrictor=None, *,
                 typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(var, body, restrictor, typ=typ, **kwargs)

    def to_conjunction(self, assignment=None):
        if self.vacuous():
            return derived(self.body.copy(), self, "trivial ∀ elimination")
        if self.finite_safe():
            a = self.scope_assignment(assignment=assignment)
            subs = [self[1].under_assignment(a | {self.varname : elem})
                    for elem in self.domain_iter()]
            return derived(boolean.BinaryAndExpr.join(subs, empty=true_term),
                self,
                f"∀{self.varname} => ∧")
        return self

    def eliminate(self, assignment=None, **sopts):
        return self.to_conjunction(assignment=assignment)

    def _compile(self):
        if self.vacuous():
            return lambda context: True
        if not self.finite_safe():
            raise meta.DomainError(self.var_instance, self.get_domain(), "Compiled ∀ quantification requires a guaranteed finite/enumerable domain")
        # compile *with* a specific domain
        # XX this is a bit slow to access; an iterator is faster but doesn't work
        # for compilation because it's not resettable
        domain = tuple(e._compiled for e in self.domain_iter())
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            for elem in domain:
                context[self.varname] = elem(context)
                if not body(context):
                    if old is not None:
                        context[self.varname] = old
                    return False
            if old is not None:
                context[self.varname] = old
            return True
        return c

    def simplify(self,assignment=None, **sopts):
        self = super().simplify()
        if self.empty_domain():
            return derived(true_term, self, "∀ triviality with empty domain")
        elif self.vacuous():
            return derived(self.body.copy(), self, "trivial ∀ elimination")
        elif self.domain_cardinality() == 1:
            # because elimination can change so much, it's hard to avoid
            # restarting simplify_all. (Among other reasons, it can create
            # new reduction targets...)
            return self.eliminate(assignment=assignment).simplify_all(assignment=assignment, **sopts)
        elif (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self.finite_safe()
                    and (self.restrictor is None or is_concrete(self.restrictor))):
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            for elem in self.domain_iter():
                a[self.varname] = meta.MetaTerm(elem, typ=self[0].type)
                # XX how to handle OutOfDomain
                # XX should this call simplify_all or something more targeted?
                cur = body.under_assignment(a, track_all_names=True).simplify_all(**sopts)
                if cur == False:
                    if cur.derivation:
                        reason = f"counterexample for ∀{self.varname}"
                    else:
                        # no subderivation to show the counterexample; show it
                        # directly
                        reason = f"counterexample for ∀{self.varname} ({self.varname}={elem})"
                    return derived(false_term, self,
                        reason,
                        subexpression=cur,
                        force_on_recurse=True,
                        note=a[self.varname])
                elif cur == True:
                    continue
                else:
                    # somehow, failed to simplify...abort
                    return self
            # only verifiers found
            # stitch together a derivation using the latest `cur`.
            a[self.varname] = self[0]
            generic_body = deriv_generic(cur,
                self[1].under_assignment(a).simplify_all(**sopts),
                self.varname)
            return derived(true_term, self, "∀ evaluation",
                subexpression=generic_body,
                force_on_recurse=True)
        return self


class Exists(RestrictedBindingOp):
    """Existential quantifier"""
    canonical_name = "Exists"
    op_name_uni="∃"
    op_name_latex="\\exists{}"

    def __init__(self, var, body, /, restrictor=None, *,
                typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(var, body, restrictor, typ=typ, **kwargs)

    def to_disjunction(self, assignment=None):
        if self.finite_safe():
            a = self.scope_assignment(assignment=assignment)
            subs = [self[1].under_assignment(a | {self.varname : elem})
                    for elem in self.domain_iter()]
            return derived(boolean.BinaryOrExpr.join(subs, empty=false_term),
                self,
                f"∃{self.varname} => ∨")
        return self

    def eliminate(self, assignment=None, **sopts):
        return self.to_disjunction(assignment=assignment)

    def _compile(self):
        empty = self.empty_domain()
        if empty:
            return lambda context: False
        elif self.vacuous() and empty == False:
            return lambda context: self[1]._compiled(context)

        if not self.finite_safe():
            raise meta.DomainError(self.var_instance, self.get_domain(), "Compiled ∃ quantification requires a guaranteed finite/enumerable domain")

        domain = tuple(self.domain_iter())
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            for elem in domain:
                context[self.varname] = elem
                if body(context):
                    if old is not None:
                        context[self.varname] = old
                    return True
            if old is not None:
                context[self.varname] = old
            return False
        return c

    def simplify(self, assignment=None, **sopts):
        empty = self.empty_domain()
        if empty:
            return derived(false_term, self, "∃ triviality with empty domain")
        elif self.vacuous():
            if empty == False:
                return derived(self.body.copy(), self, "trivial ∃ elimination")
            # fallthrough: emptiness can't be determined syntactically
            # XX when `len` is implemented, just produce len(domain) > 0?
        elif self.domain_cardinality() == 1:
            # because elimination can change so much, it's hard to avoid
            # restarting simplify_all. (Among other reasons, it can create
            # new reduction targets...)
            return self.eliminate(assignment=assignment).simplify_all(assignment=assignment, **sopts)
        if (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self.finite_safe()
                    and (self.restrictor is None or is_concrete(self.restrictor))):
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            for elem in self.domain_iter():
                a[self.varname] = meta.MetaTerm(elem, typ=self[0].type)
                # XX how to handle OutOfDomain
                cur = body.under_assignment(a, track_all_names=True).simplify_all(**sopts)
                if cur == False:
                    continue
                elif cur == True:
                    if cur.derivation:
                        reason = f"verifier for ∃{self.varname}"
                    else:
                        # no subderivation to show the verifier; show it
                        # directly
                        reason = f"verifier for ∃{self.varname} ({self.varname}={elem})"

                    return derived(true_term,
                        self,
                        reason,
                        subexpression=cur,
                        force_on_recurse=True,
                        note=a[self.varname])
                else:
                    # somehow, failed to simplify...
                    return self
            # no verifiers found
            a[self.varname] = self[0]
            generic_body = deriv_generic(cur,
                self[1].under_assignment(a).simplify_all(**sopts),
                self.varname)
            return derived(false_term, self, f"no verifiers for ∃{self.varname}",
                subexpression=generic_body,
                force_on_recurse=True)

        return self


# shared code for ∃! and ι; this could probably be much further generalized
def find_unique_evaluation(domain, te, f, varname, assignment):
    found = None
    found_te = None
    cur = None
    for elem in domain:
        assignment[varname] = elem
        # XX how to handle OutOfDomain
        cur = f(te.under_assignment(assignment, track_all_names=True))
        if cur == True:
            if found is None:
                found = elem
                found_te = cur
                continue
            return None, (found, elem), (found_te, cur)
        elif cur == False:
            continue
        else:
            # somehow, failed to simplify...
            return None, te, None
    if found_te is None:
        # provide the last `cur` (if any) to be used in creating a derivation
        found_te = cur
    return found, None, found_te


class ExistsExact(RestrictedBindingOp):
    """Existential quantifier requiring unique existence"""
    canonical_name = "ExistsExact"
    op_name_uni="∃!"
    op_name_latex="\\exists{}!"

    @classmethod
    def _setup_impl(cls):
        if getattr(cls, '_impl_restricted', None) is not None:
            return
        # combinators for the `eliminate` implementation for ExistsExact
        # note: these are (and have to be) let-bound!
        cls._impl_restricted = te(
            "L f_<X,t> : L r_{X} : Exists x_X << r : f(x) & (Forall y_X << r : f(y) >> x <=> y)")
        cls._impl_unrestricted = te(
            "L f_<X,t> : Exists x_X : f(x) & (Forall y_X : f(y) >> x <=> y)")

    def __init__(self, var, body, /, restrictor=None, *,
                typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(var, body, restrictor=restrictor, typ=typ, **kwargs)

    def eliminate(self, assignment=None, **sopts):
        self._setup_impl()

        fun = LFun(self[0], self[1])

        if self.restricted():
            result = self._impl_restricted(fun)(self.restrictor)
        else:
            result = self._impl_unrestricted(fun)

        # suppress derivations for the reduction; we can't shortcut using
        # apply because this characteristically involves multiple reduction
        # steps
        with ply.no_derivations():
            result = result.reduce_all()
        return derived(result, self, "∃! elimination")

    def _compile(self):
        empty = self.empty_domain()
        if empty:
            return lambda context: False
        if not self.finite_safe():
            raise meta.DomainError(self.var_instance, self.get_domain(), "Compiled ∃! quantification requires a guaranteed finite/enumerable domain")
        # vacuous case requires domain size exactly 1, just use the full
        # calculation:
        domain = tuple(e._compiled for e in self.domain_iter())
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            found = None
            for elem in domain:
                context[self.varname] = elem(context)
                if body(context):
                    if found is not None:
                        if old is not None:
                            context[self.varname] = old
                        return False # found 2
                    else:
                        found = elem
            if old is not None:
                context[self.varname] = old
            return found is not None
        return c

    def simplify(self, assignment=None, **sopts):
        empty = self.empty_domain()
        if empty:
            return derived(false_term, self, "∃! triviality with empty domain")
        elif self.vacuous() and not self.restricted():
            # we need to handle this case for simplification generality
            # XX domain restriction cases are unhandled, but should be handled
            if self.domain_cardinality() == None:
                return self # XX can't be determined. Will lead to crashes in simplification...
            elif self.domain_cardinality() == 0:
                # is this possible?
                return derived(false_term, self, "Vacuous ∃! with empty domain")
            elif self.domain_cardinality() == 1:
                return derived(self.body, self, "Vacuous ∃! with singleton domain")
            else:
                return derived(false_term, self, "Vacuous ∃! with non-trivial domain")
        elif self.domain_cardinality() == 1:
            # this is quite cumbersome, but it works out
            return self.eliminate(assignment=assignment).simplify_all(**sopts)
        elif (get_sopt('evaluate', sopts)
                        and not self.free_terms()
                        and self.finite_safe()
                        and (self.restrictor is None or is_concrete(self.restrictor))):
            # vacuous binding case is handled here
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            verifier, counterexample, sub = find_unique_evaluation(
                self.domain_iter(),
                body,
                (lambda t : ply.simplify_all(t, **sopts)),
                self.varname,
                a)
            if counterexample is self[1]:
                return self
            elif verifier is not None:
                return derived(true_term, self,
                        f"unique verifier for ∃!{self.varname}",
                        subexpression=sub,
                        force_on_recurse=True,
                        note=verifier)
            elif counterexample is not None:
                # XX this derivation is a bit clunky
                if sub is None:
                    if (isinstance(counterexample, BindingOp)
                                and counterexample.get_type_env().type_var_set):
                        # this can happen with some vacuous ExistsExact cases
                        # where the domain can't actually be determined. It
                        # would be nice to head this off earlier and/or fix,
                        # but at least the case where the bound variable can
                        # be detected here, and probably shouldn't error.
                        return self
                    raise ValueError(
                        f"Bug: `find_unique_evaluation` failed to simplify subexpression `{repr(counterexample)}` of `{repr(self)}` during evaluation; assignment {repr(a)}")
                r = derived(false_term, self,
                        f"counterexample for ∃!{self.varname}",
                        subexpression=sub[0],
                        force_on_recurse=True)
                return derived(r, r,
                        f"counterexample for ∃!{self.varname}",
                        subexpression=sub[1],
                        force_on_recurse=True,
                        allow_trivial=True,
                        note=counterexample) # store both as a tuple in the note field
            else:
                if sub is not None:
                    a[self.varname] = self[0]
                    generic_body = deriv_generic(sub,
                        self[1].under_assignment(a).simplify_all(**sopts),
                        self.varname)
                else:
                    generic_body = None
                return derived(false_term, self, f"no verifiers for ∃!{self.varname}",
                    subexpression=generic_body,
                    force_on_recurse=True)
        return self


class Iota(RestrictedBindingOp):
    """Iota operator.  This is best construed as Fregean."""
    canonical_name = "Iota"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {"ι"}

    commutative = False # a bit meaningless, since ιx:ιy can't occur..

    def __init__(self, var, body, /, restrictor=None, *,
                typ=None, **kwargs):
        # type constraint: var and self have the same type
        var, typ = self.type_constraint(var, typ)
        super().__init__(var, body, restrictor=restrictor,
            typ=typ, body_type=types.type_t, **kwargs)
        # superclass may have updated vartype again while doing type inference
        # on the body
        self.type = self.vartype

    def _compile(self):
        # XX code dup
        if not self.finite_safe():
            raise meta.DomainError(self.var_instance, self.get_domain(), "Compiled ι quantification requires a guaranteed finite/enumerable domain")
        domain = tuple(e._compiled for e in self.domain_iter())
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            found = None
            for elem in domain:
                # assumption: x is uncompiled
                context[self.varname] = elem(context)
                if body(context):
                    if found is not None:
                        if old is not None:
                            context[self.varname] = old
                        # XX is the restrictor adequately described in these
                        # errors?
                        raise meta.DomainError(self, self.get_domain(),
                            extra="Uniqueness failure on compiled ι")
                    else:
                        found = context[self.varname]
            if old is not None:
                context[self.varname] = old
            if found is None:
                raise meta.DomainError(self, self.get_domain(),
                    extra="Existence failure on compiled ι")
            return found
        return c

    def eliminate(self, assignment=None, **sopts):
        return self.simplify(assignment=assignment, **sopts)

    def simplify(self, assignment=None, **sopts):
        if (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self.finite_safe()
                    and (self.restrictor is None or is_concrete(self.restrictor))):
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            verifier, counterexample, sub = find_unique_evaluation(
                self.domain_iter(),
                body,
                (lambda t : ply.simplify_all(t, **sopts)),
                self.varname,
                self.scope_assignment(assignment=assignment))
            if verifier is not None:
                return derived(meta.MetaTerm(verifier, typ=self[0].type),
                                self, f"unique instantiation for ι",
                                subexpression=sub, force_on_recurse=True)
            else:
                if counterexample is None:
                    extra = "existence failure on ι simplification"
                else:
                    if sub is None:
                        raise ValueError(
                            f"Bug: `find_unique_evaluation` failed to simplify subexpression `{repr(counterexample)}` of `{repr(self)}` during evaluation")
                    extra = f"uniqueness failure on ι simplification; counterexamples: `{repr(counterexample)}`"
                raise meta.DomainError(self, self.get_domain(), extra=extra)
        return self

class IotaPartial(Iota):
    canonical_name = "IotaPartial"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {}
    pre_simplify = True

    def __init__(self, var, body, /, restrictor=None, **kwargs):
        super().__init__(var, body, restrictor=restrictor, **kwargs)

    def _compile(self):
        # pretty simple: defer to the `Partial` object generated by simplify.
        # this does not do recursive simplification.
        return self.simplify()._compiled

    def calculate_partiality(self, vars=None, **sopts):
        new_body = self.body.calculate_partiality(vars=vars, **sopts)
        # defer any further calculation if there are bound variables in the body
        # (probably not technically necessary?)
        if vars is not None:
            if vars & new_body.free_variables():
                return derived(self.copy_local(self.var_instance, new_body),
                                            self, "Partiality (Iota body only)")
        if isinstance(new_body, Partial):
            new_body = new_body.body & new_body.condition
        new_condition = new_body.copy()

        new_body = Iota(self.var_instance, new_body, restrictor=self.restrictor)
        if self.varname in new_condition.free_variables():
            new_condition = ExistsExact(self.var_instance, new_condition, restrictor=self.restrictor)
        return derived(Partial(new_body, new_condition), self,
                                                    "Partiality (Iota expansion)")

    def simplify(self, **sopts):
        # it's part of the semantics that this converts to a completely
        # different value, so do it unconditionally as part of simplify.
        # (This class is marked with `pre_simplify`.)
        # XX the division of labor between these is weird, and doing this
        # without checking for bound vars could lead to problems?
        return self.calculate_partiality(**sopts)


# backwards compatibility versions of these quantifiers that are strictly
# unary

class ExistsUnary(Exists):
    # canonical_name = "Exists"
    # op_name_uni="∃"
    # op_name_latex="\\exists{}"
    allow_restrictor = False

    def __init__(self, var, body, **kwargs):
        super().__init__(var, body, restrictor=None, **kwargs)


class ForallUnary(Forall):
    """Universal unary quantifier"""
    # canonical_name = "Forall"
    # op_name_uni = "∀"
    # op_name_latex = "\\forall{}"
    allow_restrictor = False

    def __init__(self, var, body, **kwargs):
        super().__init__(var, body, restrictor=None, **kwargs)


class IotaUnary(Iota):
    allow_restrictor = False

    def __init__(self, var, body, **kwargs):
        super().__init__(var, body, restrictor=None, **kwargs)
