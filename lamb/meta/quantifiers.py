import lamb
from lamb import types, utils
from .core import op, derived, registry, TypedExpr, TypedTerm, SyncatOpExpr
from .core import BindingOp, Partial, LFun, get_sopt
from . import meta, ply, boolean
from .boolean import true_term, false_term
from lamb.types import type_t
from lamb.utils import dbg_print


def setup_operators():
    registry.add_binding_op(ForallUnary)
    registry.add_binding_op(ExistsUnary)
    registry.add_binding_op(ExistsExact)
    registry.add_binding_op(IotaUnary)
    registry.add_binding_op(IotaPartial)


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


class ForallUnary(BindingOp):
    """Universal unary quantifier"""
    canonical_name = "Forall"
    op_name_uni = "∀"
    op_name_latex = "\\forall{}"

    def __init__(self, var, body, varname=None, vartype=None, assignment=None,
                                                            type_check=True):
        super().__init__(var, body, typ=types.type_t,
            varname=varname, vartype=vartype,
            assignment=assignment, type_check=type_check)

    def to_conjunction(self, assignment=None):
        if self[0].type.domain.finite:
            a = self.scope_assignment(assignment=assignment)
            subs = [self[1].under_assignment(a | {self.varname : meta.MetaTerm(elem, typ=self[0].type)})
                    for elem in self[0].type.domain]
            return derived(boolean.BinaryAndExpr.join(subs, empty=True),
                self,
                f"∀{self.varname} => ∧")
        return self

    def eliminate(self, assignment=None, **sopts):
        return self.to_conjunction(assignment=assignment)

    def _compile(self):
        if not (self[0].type.domain.enumerable() and self[0].type.domain.finite):
            raise NotImplementedError("Compiled ∀ quantification requires a guaranteed finite/enumerable domain")
        if self.vacuous():
            return lambda context: True
        # compile *with* a specific domain
        # XX this is a bit slow to access; an iterator is faster but doesn't work
        # for compilation because it's not resettable
        domain = tuple(self[0].type.domain)
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            for elem in domain:
                context[self.varname] = elem
                if not body(context):
                    if old is not None:
                        context[self.varname] = old
                    return False
            if old is not None:
                context[self.varname] = old
            return True
        return c

    def simplify(self,assignment=None, **sopts):
        # note: not valid if the domain of individuals is completely empty
        # (would return True). We are therefore assuming that this case is
        # ruled out a priori.
        if not self.varname in self.body.free_variables():
            return derived(self.body.copy(), self, "trivial ∀ elimination")
        elif self.type.domain.cardinality() == 0:
            return derived(true_term, self, "∀ triviality with empty domain")
        elif (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self[0].type.domain.enumerable()
                    and self[0].type.domain.finite):
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            for elem in self[0].type.domain:
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
                    # somehow, failed to simplify...
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

class ExistsUnary(BindingOp):
    """Existential unary quantifier"""
    canonical_name = "Exists"
    op_name_uni="∃"
    op_name_latex="\\exists{}"

    def __init__(self, var, body,
                varname=None, vartype=None, assignment=None, type_check=True):
        super().__init__(var, body, types.type_t,
            varname=varname, vartype=vartype,
            assignment=assignment, type_check=type_check)

    def to_disjunction(self, assignment=None):
        if self[0].type.domain.enumerable() and self[0].type.domain.finite:
            a = self.scope_assignment(assignment=assignment)
            subs = [self[1].under_assignment(a | {self.varname : meta.MetaTerm(elem, typ=self[0].type)})
                    for elem in self[0].type.domain]
            return derived(boolean.BinaryOrExpr.join(subs, empty=False),
                self,
                f"∃{self.varname} => ∨")
        return self

    def eliminate(self, assignment=None, **sopts):
        return self.to_disjunction(assignment=assignment)

    def _compile(self):
        if not (self[0].type.domain.enumerable() and self[0].type.domain.finite):
            raise NotImplementedError("Compiled ∃ quantification requires a guaranteed finite/enumerable domain")
        if self.vacuous():
            return lambda context: False
        domain = tuple(self[0].type.domain)
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
        if not self.varname in self.body.free_variables():
            # note: not valid if the domain is completely empty.
            # it's a bit silly to check for this, but let's be exact:
            if self.type.domain.cardinality() == 0:
                return derived(false_term, self, "∃ triviality with empty domain")
            else:
                return derived(self.body.copy(), self, "trivial ∃ elimination")
        elif (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self[0].type.domain.enumerable()
                    and self[0].type.domain.finite):
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            for elem in self[0].type.domain:
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


class ExistsExact(BindingOp):
    """Existential unary quantifier"""
    canonical_name = "ExistsExact"
    op_name_uni="∃!"
    op_name_latex="\\exists{}!"

    def __init__(self, var, body,
                varname=None, vartype=None, assignment=None, type_check=True):
        super().__init__(var, body, types.type_t,
            varname=varname, vartype=vartype,
            assignment=assignment, type_check=type_check)

    def eliminate(self, **sopts):
        var1 = self[0].copy()
        var2 = TypedTerm(self[1].find_safe_variable(starting=self.varname), typ=var1.type)
        fun = LFun(var1.copy(), self[1])
        result = ExistsUnary(var1, fun.apply(var1) & ForallUnary(var2, fun.apply(var2) >> var1.equivalent_to(var2)))
        result = derived(result, self, "∃! elimination")
        return result

    def _compile(self):
        if not (self[0].type.domain.enumerable() and self[0].type.domain.finite):
            raise NotImplementedError("Compiled ∃! quantification requires a guaranteed finite/enumerable domain")
        if self.vacuous():
            return lambda context: False
        domain = tuple(self[0].type.domain)
        body = self[1]._compiled
        def c(context):
            old = context.get(self.varname, None)
            found = None
            for elem in domain:
                context[self.varname] = elem
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
        if not self.varname in self.body.free_variables():
            # even sillier to check for than the ∃ case...
            c = self.type.domain.cardinality()
            if c == 1:
                return derived(true_term, self, "∃! triviality (cardinality 1)")
            else:
                reason = c == 0 and "empty domain" or "cardinality > 1"
                return derived(false_term, self, f"∃! triviality ({reason})")
        elif (get_sopt('evaluate', sopts)
                        and not self.free_terms()
                        and self[0].type.domain.enumerable()
                        and self[0].type.domain.finite):
            a = self.scope_assignment(assignment=assignment)
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            verifier, counterexample, sub = find_unique_evaluation(
                self[0].type.domain,
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


# maybe should be elsewhere?
class IotaUnary(BindingOp):
    """Iota operator.  This is best construed as Russellian."""
    canonical_name = "Iota"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {"ι"}

    commutative = False # a bit meaningless, since ιx:ιy can't occur..

    def __init__(self, var, body,
                varname=None, vartype=None, assignment=None, type_check=True):
        super().__init__(var, body, typ=None,
            varname=varname, vartype=vartype, body_type=types.type_t,
            assignment=assignment, type_check=type_check)
        self.type = self.vartype

    def to_test(self, x):
        """Build a boolean test by substituting `x` into the body."""
        return LFun(self.var_instance, self.body).apply(x)

    def try_adjust_type_local(self, unified_type, derivation_reason, env):
        sub_var = TypedTerm(self.varname, unified_type)
        # TODO: does this need to pass in assignment?
        new_condition = self.to_test(sub_var)
        result = self.copy_local(sub_var, new_condition)
        return result

    def _compile(self):
        # XX code dup
        if not (self[0].type.domain.enumerable() and self[0].type.domain.finite):
            raise NotImplementedError("Compiled ∃! quantification requires a guaranteed finite/enumerable domain")
        if self.vacuous():
            return lambda context: False
        domain = tuple(self[0].type.domain)
        body = self[1]._compiled
        def c(context):
            # could pre-select the domain, but this allows for it to change
            # (to some degree)
            old = context.get(self.varname, None)
            found = None
            for elem in domain:
                # assumption: x is uncompiled
                context[self.varname] = elem
                if body(context):
                    if found is not None:
                        if old is not None:
                            context[self.varname] = old
                        raise meta.DomainError(self, self[0].type.domain,
                            extra="Uniqueness failure on compiled ι")
                    else:
                        found = context[self.varname]
            if old is not None:
                context[self.varname] = old
            if found is None:
                raise meta.DomainError(self, self[0].type.domain,
                    extra="Existence failure on compiled ι")
            return found
        return c

    def simplify(self, assignment=None, **sopts):
        if not self.varname in self.body.free_variables():
            c = self.type.domain.cardinality()
            if c == 1:
                return derived(c.domain[0], self, "ι triviality (cardinality 1)")
            else:
                # XX what should really happen here?
                return self
        elif (get_sopt('evaluate', sopts)
                    and not self.free_terms()
                    and self[0].type.domain.enumerable()
                    and self[0].type.domain.finite):
            body = self[1].simplify_all(**sopts)
            # disabling alphanorm for the loop is heuristic, but for many cases
            # doing a single pre-simplification will hopefully get scenarios
            # that alphanorm would speed up.
            sopts['alphanorm'] = False
            verifier, counterexample, sub = find_unique_evaluation(
                self[0].type.domain,
                body,
                (lambda t : ply.simplify_all(t, **sopts)),
                self.varname,
                self.scope_assignment(assignment=assignment))
            if verifier is not None:
                return derived(meta.MetaTerm(verifier, typ=self[0].type), self, f"unique instantiation for ι",
                    subexpression=sub, force_on_recurse=True)
            else:
                # return self
                if counterexample is None:
                    extra = ""
                else:
                    extra = "uniqueness failure"
                raise meta.DomainError(self, self[0].type.domain, extra=extra)
        return self

class IotaPartial(IotaUnary):
    canonical_name = "IotaPartial"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {}
    pre_simplify = True

    def __init__(self, var, body, varname=None, vartype=None, assignment=None,
                                                            type_check=True):
        super().__init__(var, body, varname=varname, vartype=vartype,
            assignment=assignment, type_check=type_check)

    # XX what should ._compiled do? For now, no implementation.

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

        new_body = IotaUnary(self.var_instance, new_body)
        if self.varname in new_condition.free_variables():
            new_condition = ExistsExact(self.var_instance, new_condition)
        return derived(Partial(new_body, new_condition), self,
                                                    "Partiality (Iota expansion)")

    def simplify(self, **sopts):
        # it's part of the semantics that this converts to a completely
        # different value, so do it unconditionally as part of simplify.
        # (This class is marked with `pre_simplify`.)
        # XX the division of labor between these is weird, and doing this
        # without checking for bound vars could lead to problems?
        return self.calculate_partiality(**sopts)
