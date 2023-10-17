import lamb
from lamb import types
from .core import op, derived, registry, TypedExpr, TypedTerm, SyncatOpExpr, BindingOp, Partial, LFun
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


# for whatever reason, monkey patching __bool__ doesn't work.
# TODO: is this a good idea?
class FalseTypedTerm(TypedTerm):
    def __bool__(self):
        # override TypedExpr.__bool__: it returns True for everything else.
        return False

true_term = TypedTerm("True", type_t)
false_term = FalseTypedTerm("False", type_t)

# simplify principle: implement simplification that can be handled by reasoning
# about constants, otherwise leave for the future. The goal of this code is
# not to implement a prover.

# proof of concept for now: the rest of the logical operators do not quite
# work as pure python
@op("~", type_t, type_t, op_uni="¬", op_latex="\\neg{}", deriv_desc="negation", python_only=False)
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

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self):
        def d(x, desc="conjunction"):
            return derived(x, self, desc=desc)
        if self.args[0] == false_term or self.args[1] == false_term:
            return d(false_term)
        elif self.args[0] == true_term:
            return d(self.args[1].copy())
        elif self.args[1] == true_term:
            return d(self.args[0].copy())
        elif self.args[0] == self.args[1]:
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p & p` to just p.
            return d(self.args[0].copy())
        elif (isinstance(self.args[0], UnaryNegExpr) and self.args[0][0] == self.args[1]
                or isinstance(self.args[1], UnaryNegExpr) and self.args[1][0] == self.args[0]):
            # *heuristic* simplification rule: non-contradiction law,
            # simplify `p & ~p` to just False.
            return d(false_term, desc="non-contradiction")
        else:
            return self


class BinaryOrExpr(SyncatOpExpr):
    canonical_name = "|"
    op_name_uni = "∨"
    op_name_latex = "\\vee{}"
    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self):
        def d(x, desc="disjunction"):
            return derived(x, self, desc=desc)
        if self.args[0] == true_term or self.args[1] == true_term:
            return d(true_term)
        elif self.args[0] == false_term:
            # covers case of False | False
            return d(self.args[1].copy())
        elif self.args[1] == false_term:
            return d(self.args[0].copy())
        elif self.args[0] == self.args[1]:
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p | p` to just p.
            return d(self.args[0].copy())
        elif (isinstance(self.args[0], UnaryNegExpr) and self.args[0][0] == self.args[1]
                or isinstance(self.args[1], UnaryNegExpr) and self.args[1][0] == self.args[0]):
            # *heuristic* simplification rule: excluded middle,
            # simplify `p | ~p` to just True.
            return d(true_term, desc="excluded middle")
        else:
            return self


class BinaryArrowExpr(SyncatOpExpr):
    canonical_name = ">>"
    op_name_uni = "→"
    op_name_latex = "\\rightarrow{}"

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self):
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

    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self):
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
        else:
            return self


# TODO: generalize this?
class BinaryNeqExpr(SyncatOpExpr):
    canonical_name = "^"
    secondary_names = {"=/="}
    op_name_uni = "≠"
    op_name_latex = "\\not="
    def __init__(self, arg1, arg2):
        super().__init__(type_t, arg1, arg2)

    def simplify(self):
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
# them to work.

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

    def simplify(self):
        # note: not valid if the domain of individuals is completely empty
        # (would return True). We are therefore assuming that this case is
        # ruled out a priori.
        if not self.varname in self.body.free_variables():
            return self.body
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

    def simplify(self):
        # note: not valid if the domain of individuals is completely empty
        # (would return False)
        if not self.varname in self.body.free_variables():
            return self.body
        return self

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


# maybe should be elsewhere?
class IotaUnary(BindingOp):
    """Iota operator.  This is best construed as Russellian."""
    canonical_name = "Iota"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {"ι"}

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


class IotaPartial(IotaUnary):
    canonical_name = "IotaPartial"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {}

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
        if vars is not None:
            if vars | new_body.free_variables():
                return derived(self.copy_local(self.var_instance, new_body),
                                            self, "Partiality simplification")
        if isinstance(new_body, Partial):
            new_body = new_body.body & new_body.condition
        new_condition = new_body.copy()

        new_body = IotaUnary(self.var_instance, new_body)
        if self.varname in new_condition.free_variables():
            new_condition = ExistsExact(self.var_instance, new_condition)
        return derived(Partial(new_body, new_condition), self,
                                                    "Partiality simplification")


pure_ops = {UnaryNegExpr, BinaryAndExpr, BinaryOrExpr, BinaryArrowExpr,
            BinaryNeqExpr, BinaryBiarrowExpr}

def is_pure(e):
    if isinstance(e, TypedTerm) and e.type == type_t:
        return True
    elif e.__class__ not in pure_ops:
        return False
    else:
        return all(is_pure(a) for a in e.args)

# TODO: run these with time-based timeouts, rather than heuristic maxes

# warning, exponential in both time and space in the size of l...
def all_boolean_combos(l, cur=None, max_length=20):
    # 20 here is somewhat arbitrary: it's about where exponential blowup gets
    # noticeable on a reasonably fast computer
    if len(l) > max_length:
        raise ValueError("Tried to calculate boolean combos for too long a sequence: %s" % repr(l))
    if cur is None:
        cur = dict()
    if len(l) == 0:
        return [cur]
    remainder = l[1:]
    if l[0] == 'True' or l[0] == 'False':
        # this is a bit messy, but we are dealing with term names a this point
        cur[l[0]] = l[0] == 'True' and True or False
        return all_boolean_combos(remainder, cur)
    cur_false = cur.copy()
    cur[l[0]] = True
    cur_false[l[0]] = False
    return all_boolean_combos(remainder, cur) + all_boolean_combos(remainder, cur_false)

def truthtable(e, max_length=12):
    """
    Calculate a full truth-table for a pure boolean expression `e`. This is a
    brute-force calculation, and so is exponential (time and space) in the
    number of terms.
    """
    se = e.simplify_all() # maybe not what you'd want?
    if not is_pure(se):
        raise ValueError("Cannot produce a truthtable for a non-boolean TypedExpr")
    terms = list(se.get_type_env().var_mapping.keys())
    terms.sort()
    # 12 here is once again just chosen as a default heuristic
    if len(terms) > max_length:
        raise ValueError("Tried to calculate truthtable for too long a sequence: %s" % repr(e))
    in_tvs = all_boolean_combos(terms)
    return [(v, e.under_assignment(v).simplify_all()) for v in in_tvs]

def truthtable_equiv(e1, e2):
    return truthtable(e1) == truthtable(e2)

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
