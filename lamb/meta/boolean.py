import lamb
from lamb import types
from .core import op, derived, registry, TypedExpr, TypedTerm, SyncatOpExpr
from .core import BindingOp, Partial, LFun, get_sopt
from .meta import MetaTerm
from .ply import simplify_all, alphanorm
from lamb.types import type_t

global true_term, false_term

def setup_operators():
    def add_t_op(c):
        registry.add_operator(c, *[type_t for x in range(c.arity)])

    add_t_op(UnaryNegExpr)
    add_t_op(BinaryAndExpr)
    add_t_op(BinaryOrExpr)
    add_t_op(BinaryArrowExpr)
    add_t_op(BinaryNeqExpr)
    add_t_op(BinaryBiarrowExpr)
    # questionable whether these should be here, but t is the minimum that
    # is needed for these operators.
    registry.add_binding_op(ForallUnary)
    registry.add_binding_op(ExistsUnary)
    registry.add_binding_op(ExistsExact)
    registry.add_binding_op(IotaUnary)
    registry.add_binding_op(IotaPartial)

true_term = MetaTerm(True)
false_term = MetaTerm(False)

# simplify principle: implement simplification that can be handled by reasoning
# about constants, otherwise leave for the future. The goal of this code is
# not to implement a prover.

# proof of concept for now: the rest of the logical operators do not quite
# work as pure python
@op("~", type_t, type_t, op_uni="¬", op_latex="\\neg{}", deriv_desc="negation elimination", python_only=False)
def UnaryNegExpr(self, x):
    if isinstance(x, TypedExpr):
        if isinstance(x, UnaryNegExpr):
            return x[0].copy()
        else:
            return self
    else:
        return not x


# could make a factory function for these
class BinaryAndExpr(SyncatOpExpr):
    canonical_name = "&"
    op_name_uni = "∧"
    op_name_latex = "\\wedge{}"
    commutative = True
    associative = True

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    @classmethod
    def simplify_early_check(cls, e1, e2, origin=None, **sopts):
        for e in (e1,e2):
            if e == false_term:
                if origin is None:
                    origin = e
                return derived(false_term, origin,
                    "conjunction (elimination on `False`)", allow_trivial=True)
        return None

    @classmethod
    def simplify_args(cls, e1, e2, origin=None, **sopts):
        if origin is None:
            origin = e1 & e2
        elim = cls.simplify_early_check(e1, e2, origin=origin)
        if elim is not None:
            return elim
        def d(x, desc="conjunction"):
            return derived(x, origin, desc=desc)

        if e1 == true_term:
            return d(e2.copy())
        elif e2 == true_term:
            return d(e1.copy())
        elif e1 == e2:
            # *syntactic* idempotence
            return d(e1.copy(), desc="conjunction (idempotence)")
        elif (isinstance(e1, UnaryNegExpr) and e1[0] == e2
                or isinstance(e2, UnaryNegExpr) and e2[0] == e1):
            # *syntactic* non-contradiction
            return d(false_term, desc="non-contradiction")
        else:
            return None


class BinaryOrExpr(SyncatOpExpr):
    canonical_name = "|"
    op_name_uni = "∨"
    op_name_latex = "\\vee{}"
    commutative = True
    associative = True

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    @classmethod
    def simplify_early_check(cls, e1, e2, origin=None, **sopts):
        for e in (e1,e2):
            if e == true_term:
                if origin is None:
                    origin = e
                return derived(true_term, origin,
                    "disjunction (elimination on `True`)", allow_trivial=True)
        return None


    @classmethod
    def simplify_args(cls, e1, e2, origin=None, **sopts):
        if origin is None:
            origin = e1 | e2
        elim = cls.simplify_early_check(e1, e2, origin=origin)
        if elim is not None:
            return elim

        def d(x, desc="disjunction"):
            return derived(x, origin, desc=desc)
        if e1 == false_term:
            # covers case of False | False
            return d(e2.copy())
        elif e2 == false_term:
            return d(e1.copy())
        elif e1 == e2:
            # *syntactic* idempotence
            return d(e1.copy(), desc="disjunction (idempotence)")
        elif (isinstance(e1, UnaryNegExpr) and e1[0] == e2
                or isinstance(e2, UnaryNegExpr) and e2[0] == e1):
            # syntactic excluded middle check
            return d(true_term, desc="excluded middle")
        else:
            return None


class BinaryArrowExpr(SyncatOpExpr):
    canonical_name = ">>"
    op_name_uni = "→"
    op_name_latex = "\\rightarrow{}"
    commutative = False
    associative = False

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self, **sopts):
        def d(x):
            return derived(x, self, desc="material implication")
        if self.args[0] == false_term:
            return d(true_term)
        elif self.args[0] == true_term:
            return d(self.args[1].copy())
        elif self.args[1] == false_term:
            return d(UnaryNegExpr(self.args[0]))
        elif self.args[1] == true_term:
            return d(true_term)
        elif self.args[0] == self.args[1]:
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p >> p` to just `true`.
            return d(true_term)
        else:
            return self

class BinaryBiarrowExpr(SyncatOpExpr):
    canonical_name = "<=>"
    secondary_names = {"=="}
    op_name_uni = "↔"
    op_name_latex = "\\leftrightarrow{}"
    commutative = True
    associative = True

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self, **sopts):
        def d(x):
            return derived(x, self, desc="biconditional")
        if self.args[0] == false_term:
            if self.args[1] == true_term:
                return d(false_term)
            elif self.args[1] == false_term:
                return d(true_term)
            else:
                return d(UnaryNegExpr(self.args[1]))
        elif self.args[0] == true_term:
            if self.args[1] == false_term:
                return d(false_term)
            elif self.args[1] == true_term:
                return d(true_term)
            else:
                return d(self.args[1].copy())
        elif self.args[1] == false_term: # term+term is already taken care of
            return d(UnaryNegExpr(self.args[0]))
        elif self.args[1] == true_term:
            return d(self.args[0].copy())
        elif self.args[0] == self.args[1]:
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p <-> p` to just `true`.
            return d(true_term)
        elif isinstance(self.args[1], BinaryAndExpr) and self.args[0] == self.args[1][0]:
            # Heuristic: `p <=> p & q` simplifies to `p >> q`. The next four
            # are all variants of this. This was added to handle some cases
            # in set simplification.
            return d(self.args[0] >> self.args[1][1])
        elif isinstance(self.args[1], BinaryAndExpr) and self.args[0] == self.args[1][1]:
            return d(self.args[0] >> self.args[1][0])
        elif isinstance(self.args[0], BinaryAndExpr) and self.args[1] == self.args[0][0]:
            return d(self.args[1] >> self.args[0][1])
        elif isinstance(self.args[0], BinaryAndExpr) and self.args[1] == self.args[0][1]:
            return d(self.args[1] >> self.args[0][0])
        else:
            return self


# TODO: generalize this?
class BinaryNeqExpr(SyncatOpExpr):
    canonical_name = "^"
    secondary_names = {"=/="}
    op_name_uni = "≠"
    op_name_latex = "\\not="
    commutative = True
    associative = True

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self, **sopts):
        def d(x):
            return derived(x, self, desc="neq")
        if self.args[0] == false_term:
            if self.args[1] == true_term:
                return d(true_term)
            elif self.args[1] == false_term:
                return d(false_term)
            else:
                return d(self.args[1].copy())
                
        elif self.args[0] == true_term:
            if self.args[1] == false_term:
                return d(true_term)
            elif self.args[1] == true_term:
                return d(false_term)
            else:
                return d(UnaryNegExpr(self.args[1]))
        elif self.args[1] == true_term: # term+term is already taken care of
            return d(UnaryNegExpr(self.args[0]))
        elif self.args[1] == false_term:
            return d(self.args[0].copy())
        elif self.args[0] == self.args[1]:
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p =/= p` to just `false`.
            return d(false_term)
        else:
            # note: don't simplify p =/= q; this would be a job for a prover
            return self

####################### Quantifiers
# These are not picky about the variable type, but t is the minimum needed for
# them to work, hence putting them in `boolean`

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

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        super().__init__(var_or_vtype, types.type_t, body, varname=varname,
                                assignment=assignment, type_check=type_check)

    def copy(self):
        return ForallUnary(self.vartype, self.body, self.varname)

    def copy_local(self, var, arg, type_check=True):
        return ForallUnary(var, arg, type_check=type_check)

    def to_conjunction(self):
        if self[0].type.domain.finite:
            a = self.scope_assignment()
            subs = [self[1].under_assignment(a | {self.varname : MetaTerm(elem)})
                    for elem in self[0].type.domain]
            return derived(BinaryAndExpr.join(subs, empty=True),
                self,
                f"∀{self.varname} => ∧")
        return self

    def eliminate(self, **sopts):
        return self.to_conjunction()

    def simplify(self, **sopts):
        # note: not valid if the domain of individuals is completely empty
        # (would return True). We are therefore assuming that this case is
        # ruled out a priori.
        if not self.varname in self.body.free_variables():
            return derived(self.body.copy(), self, "trivial ∀ elimination")
        elif self.type.domain.cardinality() == 0:
            return derived(true_term, self, "∀ triviality with empty domain")
        elif get_sopt('evaluate', sopts) and not self.free_terms() and self[0].type.domain.enumerable():
            a = self.scope_assignment()
            for elem in self[0].type.domain:
                a[self.varname] = MetaTerm(elem)
                # XX how to handle OutOfDomain
                # XX should this call simplify_all or something more targeted?
                cur = self[1].under_assignment(a, track_all_names=True).simplify_all(**sopts)
                if cur == False:
                    return derived(false_term, self,
                        f"counterexample for ∀{self.varname}",
                        subexpression=cur,
                        force_on_recurse=True)
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

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        super().__init__(var_or_vtype, types.type_t, body, varname=varname,
                    assignment=assignment, type_check=type_check)

    def copy(self):
        return ExistsUnary(self.vartype, self.body, self.varname)

    def copy_local(self, var, arg, type_check=True):
        return ExistsUnary(var, arg, type_check=type_check)        

    def to_disjunction(self):
        if self[0].type.domain.enumerable():
            a = self.scope_assignment()
            subs = [self[1].under_assignment(a | {self.varname : MetaTerm(elem)})
                    for elem in self[0].type.domain]
            return derived(BinaryOrExpr.join(subs, empty=False),
                self,
                f"∃{self.varname} => ∨")
        return self

    def eliminate(self, **sopts):
        return self.to_disjunction()

    def simplify(self, **sopts):
        if not self.varname in self.body.free_variables():
            # note: not valid if the domain is completely empty.
            # it's a bit silly to check for this, but let's be exact:
            if self.type.domain.cardinality() == 0:
                return derived(false_term, self, "∃ triviality with empty domain")
            else:
                return derived(self.body.copy(), self, "trivial ∃ elimination")
        elif get_sopt('evaluate', sopts) and not self.free_terms() and self[0].type.domain.enumerable():
            a = self.scope_assignment()
            for elem in self[0].type.domain:
                a[self.varname] = MetaTerm(elem)
                # XX how to handle OutOfDomain
                cur = self[1].under_assignment(a, track_all_names=True).simplify_all(**sopts)
                if cur == False:
                    continue
                elif cur == True:
                    return derived(true_term,
                        self,
                        f"verifier for ∃{self.varname}",
                        subexpression=cur,
                        force_on_recurse=True)
                else:
                    # somehow, failed to simplify...
                    return self
            # no verifiers found
            a[self.varname] = self[0]
            generic_body = deriv_generic(cur,
                self[1].under_assignment(a).simplify_all(**sopts),
                self.varname)
            return derived(false_term, self, "no verifiers for ∃",
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

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        super().__init__(var_or_vtype, types.type_t, body, varname=varname,
                                assignment=assignment, type_check=type_check)

    def copy(self):
        return ExistsExact(self.vartype, self.body, self.varname)

    def copy_local(self, var, arg, type_check=True):
        return ExistsExact(var, arg, type_check=type_check)        

    def eliminate(self, **sopts):
        var1 = self[0].copy()
        var2 = TypedTerm(self[1].find_safe_variable(starting=self.varname), typ=var1.type)
        fun = LFun(var1.copy(), self[1])
        result = ExistsUnary(var1, fun(var1) & ForallUnary(var2, fun(var2) >> var1.equivalent_to(var2)))
        result = derived(result, self, "∃! elimination")
        return result.reduce_all()

    def simplify(self, **sopts):
        if not self.varname in self.body.free_variables():
            # even sillier to check for than the ∃ case...
            c = self.type.domain.cardinality()
            if c == 1:
                return derived(true_term, self, "∃! triviality (cardinality 1)")
            else:
                reason = c == 0 and "empty domain" or "cardinality > 1"
                return derived(false_term, self, f"∃! triviality ({reason})")
        elif get_sopt('evaluate', sopts) and not self.free_terms() and self[0].type.domain.enumerable():
            a = self.scope_assignment()
            verifier, counterexample, sub = find_unique_evaluation(
                self[0].type.domain,
                self[1],
                (lambda t : simplify_all(t, **sopts)),
                self.varname,
                self.scope_assignment())
            if counterexample is self[1]:
                return self
            elif verifier is not None:
                return derived(true_term, self,
                        f"unique verifier for ∃!{self.varname}",
                        subexpression=sub,
                        force_on_recurse=True)
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
                        allow_trivial=True)
            else:
                if sub is not None:
                    a[self.varname] = self[0]
                    generic_body = deriv_generic(sub,
                        self[1].under_assignment(a).simplify_all(**sopts),
                        self.varname)
                else:
                    generic_body = None
                return derived(false_term, self, f"no verifiers for ∃!",
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

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body,
            varname=varname, body_type=types.type_t, assignment=assignment,
            type_check=type_check)
        self.type = self.vartype

    def copy(self):
        return IotaUnary(self.vartype, self.body, self.varname)

    def copy_local(self, var, arg, type_check=True):
        return IotaUnary(var, arg, type_check=type_check)

    def to_test(self, x):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname).apply(x)


    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        sub_var = TypedTerm(self.varname, unified_type)
        # TODO: does this need to pass in assignment?
        new_condition = self.to_test(sub_var)
        result = self.copy_local(sub_var, new_condition)
        return result

    def simplify(self, **sopts):
        if not self.varname in self.body.free_variables():
            c = self.type.domain.cardinality()
            if c == 1:
                return derived(c.domain[0], self, "ι triviality (cardinality 1)")
            else:
                # XX what should really happen here?
                return self
        elif get_sopt('evaluate', sopts) and not self.free_terms() and self[0].type.domain.enumerable():
            verifier, counterexample, sub = find_unique_evaluation(
                self[0].type.domain,
                self[1],
                (lambda t : simplify_all(t, **sopts)),
                self.varname,
                self.scope_assignment())
            if verifier is not None:
                return derived(MetaTerm(verifier), self, f"unique instantiation for ι",
                    subexpression=sub, force_on_recurse=True)
            else:
                # it's extremely unclear what should happen for a real
                # counterexample for vanilla IotaUnary. Maybe it needs to raise
                # a python exception (cf. OutOfDomain?)
                return self
        return self

class IotaPartial(IotaUnary):
    canonical_name = "IotaPartial"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {}
    pre_simplify = True

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        super().__init__(var_or_vtype, body, varname, assignment, type_check)

    def copy(self):
        return IotaPartial(self.vartype, self.body, self.varname)

    def copy_local(self, var, arg, type_check=True):
        return IotaPartial(var, arg, type_check=type_check)

    def calculate_partiality(self, vars=None):
        new_body = self.body.calculate_partiality(vars=vars)
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
                                                    "Partiality (Iota)")

    def simplify(self, **sopts):
        # it's part of the semantics that this converts to a completely
        # different value, so do it unconditionally as part of simplify.
        # (This class is marked with `pre_simplify`.)
        # XX the division of labor between these is weird, and doing this
        # without checking for bound vars could lead to problems?
        return self.calculate_partiality()

pure_ops = {UnaryNegExpr, BinaryAndExpr, BinaryOrExpr, BinaryArrowExpr,
            BinaryNeqExpr, BinaryBiarrowExpr}


def is_pure(e):
    if e.is_atomic() and e.type == type_t:
        return True
    elif e.__class__ not in pure_ops:
        return False
    else:
        return all(is_pure(a) for a in e.args)


def to_nltk_sem_expr(e):
    # generates a version of the expression that can be parsed by nltk.
    if not is_pure(e):
        # TODO: handle predicate-arg exprs
        raise ValueError("Cannot convert '%s' to nltk.sem" % repr(e))
    def nltk_bin(op):
        return "(%s %s %s)" % (to_nltk_sem_expr(e.args[0]),
                               op,
                               to_nltk_sem_expr(e.args[1]))
    if isinstance(e, TypedTerm) and e.type == type_t:
        return e.op
    elif isinstance(e, UnaryNegExpr):
        return "-%s" % to_nltk_sem_expr(e)
    elif isinstance(e, BinaryAndExpr):
        return nltk_bin("&")
    elif isinstance(e, BinaryOrExpr):
        return nltk_bin("|")
    elif isinstance(e, BinaryArrowExpr):
        return nltk_bin("->")
    elif isinstance(e, BinaryBiarrowExpr):
        return nltk_bin("<->")
    elif isinstance(e, BinaryNeqExpr):
        return "-" + nltk_bin("<->")
    else:
        raise NotImplementedError


def to_nltk_sem(e):
    import nltk
    return nltk.sem.Expression.fromstring(to_nltk_sem_expr(e))
