import lamb
from lamb import types, utils
from .core import op, derived, registry, TypedExpr, TypedTerm, SyncatOpExpr
from .core import BindingOp, Partial, LFun, get_sopt, tp
from .meta import MetaTerm, DomainError
from .ply import simplify_all, alphanorm
from lamb.types import type_t
from lamb.utils import dbg_print

global true_term, false_term

def setup_operators():
    def add_t_op(c):
        registry.add_operator(c, *[type_t for x in range(c.arity)],
                                                    shadow_warning=False)

    add_t_op(UnaryNegExpr)
    add_t_op(BinaryAndExpr)
    add_t_op(BinaryOrExpr)
    add_t_op(BinaryArrowExpr)
    add_t_op(BinaryNeqExpr)
    add_t_op(BinaryBiarrowExpr)

    registry.add_operator(Case)

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

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(typ, arg1, arg2)

    def _compile(self):
        l = self[0]._compiled
        r = self[1]._compiled
        return lambda context: l(context) and r(context)

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

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(typ, arg1, arg2)

    def _compile(self):
        l = self[0]._compiled
        r = self[1]._compiled
        return lambda context: l(context) or r(context)

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

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(typ, arg1, arg2)

    def _compile(self):
        l = self[0]._compiled
        r = self[1]._compiled
        return lambda context: not l(context) or r(context)

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
    secondary_names = {"==", "%"}
    op_name_uni = "↔"
    op_name_latex = "\\leftrightarrow{}"
    commutative = True
    associative = True

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(typ, arg1, arg2)

    def _compile(self):
        l = self[0]._compiled
        r = self[1]._compiled
        return lambda context: l(context) == r(context)

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
    secondary_names = {"=/=", "!="}
    op_name_uni = "≠"
    op_name_latex = "\\not="
    commutative = True
    associative = True

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__(typ, arg1, arg2)

    def _compile(self):
        l = self[0]._compiled
        r = self[1]._compiled
        return lambda context: l(context) != r(context)

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


class Case(TypedExpr):
    canonical_name = 'Case'
    arg_signature = tp("(t,X,X)")

    def __init__(self, cond, if_case, else_case, *, typ=None, **kwargs):
        cond, _ = self.type_constraint(cond, types.type_t)
        if_case, typ = self.type_constraint(if_case, typ)
        if_case, else_case = self.type_constraint(if_case, else_case)
        super().__init__("Case", cond, if_case, else_case, typ=if_case.type)

    def simplify(self, **sopts):
        # note: simplify_all on this class is currently not short-circuiting, but
        # possibly it should be
        if self[0] == True:
            return derived(self[1], self, "Case simplification: True")
        elif self[0] == False:
            return derived(self[2], self, "Case simplification: False")
        else:
            return self

    def _compile(self):
        cond = self[0]._compiled
        if_case = self[1]._compiled
        # this is semi-short-circuiting, in that the else case is still compiled
        # but may never be run. Note that running this from exec will still
        # generate term errors if the else case is missing terms, but lower
        # level calls don't care
        else_case = self[2]._compiled
        def inner(context):
            if cond(context):
                return if_case(context)
            else:
                return else_case(context)
        return inner

    def latex_str(self, **kwargs):
        cases = []
        c = self
        while isinstance(c, Case):
            cases.append((c[1], c[0]))
            c = c[2]
        cases = [f"{case[0].latex_str(**kwargs)} & \\text{{if }}{case[1].latex_str(**kwargs)} \\\\" for case in cases]
        newline = '\n'
        return utils.ensuremath(
            f"\\begin{{cases}}\n{newline.join(cases)}"
            f"{c.latex_str(**kwargs)} & \\text{{otherwise}} \\end{{cases}}")


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
