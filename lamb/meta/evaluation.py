import collections.abc

import lamb
from lamb import types

from .core import TypedTerm, TypeEnv
from .boolean import true_term, false_term, pure_ops, is_pure
from lamb.types import type_t

def is_propositional(e):
    # in principle, could allow type variables here
    return e.type == types.type_t

# TODO: run these with time-based timeouts, rather than heuristic maxes
# TODO: there might be faster ways to do this with numpy arrays + broadcasting

# warning, exponential in both time and space in the size of l...
def all_boolean_combos(l, cur=None, max_length=20):
    # 20 here is somewhat arbitrary: it's about where exponential blowup gets
    # noticeable on a reasonably fast computer
    if len(l) > max_length:
        raise ValueError(f"Tried to calculate boolean combos for an overlong sequence: {repr(e)}")
    if cur is None:
        cur = dict()
    if len(l) == 0:
        return [cur]
    remainder = l[1:]
    if l[0] == 'True' or l[0] == 'False':
        # this is a bit messy, but we are dealing with term names at this point
        cur[l[0]] = l[0] == 'True' and True or False
        return all_boolean_combos(remainder, cur)
    cur_false = cur.copy()
    cur[l[0]] = True
    cur_false[l[0]] = False
    # false first for better sort order
    return all_boolean_combos(remainder, cur_false) + all_boolean_combos(remainder, cur)


def sorted_term_names(e, var_map = None):
    if var_map is None:
        var_map = e.get_type_env().var_mapping
    terms = list(var_map.keys())
    # TODO: better sort orders?
    terms.sort()
    return terms


class Evaluations(collections.abc.Sequence):
    def __init__(self, expression, assignments=None, display_assignment={}):
        if assignments is None:
            assignments = []
        self.display_assignment = display_assignment

        self.expression = expression
        var_map = expression.get_type_env().var_mapping
        self.terms = sorted_term_names(expression, var_map=var_map)
        # slightly weird, but we need to reconstruct the terms for display
        # purposes, and all we have right now is strings
        self.term_exprs = [TypedTerm(t, typ=var_map[t]) for t in self.terms]
        self.update_evals(assignments)

    def update_evals(self, assignments):
        self.evaluations = [
            (v, self.expression.under_assignment(v).simplify_all())
            for v in assignments]
        in_use = set().union(*[v.keys() for v in assignments])
        # store this as a mask on self.terms
        self.in_use = [t in in_use for t in self.terms]
    
    def __len__(self):
        return len(self.evaluations)

    def __getitem__(self, i):
        """Return a pair consisting of a valuation and the evaluation of
        the stored expression under that valuation."""
        return self.evaluations[i]

    def __eq__(self, other):
        """Return True if self and other have exactly the same set of
        evaluations. This requires syntactic term identity for the evaluated
        terms, but does not require the two expressions to be identical. For
        a completely valued expression, this therefore provides a form of
        semantic equivalence."""

        # relies on evaluations having the same sort in self and other...
        return self.evaluations == other.evaluations

    def get_valued_terms(self, expr=False):
        if expr:
            l = [e.under_assignment(self.display_assignment)
                                                    for e in self.term_exprs]
        else:
            l = self.terms
        return [t[0] for t in zip(l, self.in_use) if t[1]]
    
    def _repr_markdown_(self):
        header = ([f"| {t._repr_latex_()} " for t in self.get_valued_terms(expr=True)]
                  + [f"| {self.expression.under_assignment(self.display_assignment)._repr_latex_()}"])
        sep = ["| :---:" for col in header]
        rows = []
        def tval(t):
            if t == False or t == false_term:
                return 0
            if t == True or t == true_term:
                return 1
            try:
                return t._repr_latex_()
            except AttributeError:
                return t
        
        def tname(v, t):
            if t in v:
                return tval(v[t])
            else:
                return ""

        for row in self:
            v, result = row
            rows.append(
                [f"| {tname(v, t)}" for t in self.get_valued_terms()]
                + [f"| {tval(result)}"])

        return ("".join(header) + "|\n"
                + "".join(sep) + "|\n"
                + "".join(["".join(row) + "|\n" for row in rows]))


def truthtable_valuations(e, max_terms=12):
    """Calculate all possible valuations for type `t` terms in `e`. No other
    terms are valued."""
    var_map = e.get_type_env().var_mapping
    terms = sorted_term_names(e, var_map=var_map)
    terms = [t for t in terms if var_map[t] == types.type_t]
    # 12 here is once again just chosen as a default heuristic
    if len(terms) > max_terms:
        raise ValueError(f"Tried to calculate truthtable for an overlong sequence: {repr(e)}")
    return all_boolean_combos(terms)


def extract_boolean(*exprs):
    """Extract a pure boolean skeleton from all expressions in `exprs`,
    together with a mapping that will convert these skeletons back into
    their original forms.
    
    Note that all variables used in more than one formula must have compatible
    types, and as needed any type variables shared across expressions may be
    resolved to their principal types. Consequently, if type variables are in
    play, the resulting mapping may not recover exactly the starting
    expressions.
    
    All input expressions must be exactly type t."""

    for e in exprs:
        if not is_propositional(e):
            raise ValueError(f"Can't extract boolean frame from non-boolean `{repr(e)}`")
    mappings = {}
    mapped = {}
    env = TypeEnv()
    # ensure the types are actually mergeable...
    for e in exprs:
        env.merge(e.get_type_env())
    used_vars = set(env.var_mapping.keys())
    i = 0

    def fresh():
        nonlocal i
        i += 1
        name = f"p{i}"
        if name in used_vars:
            return fresh()
        return TypedTerm(name, typ=types.type_t)

    def extract_boolean_r(e):
        nonlocal mappings
        e = e.under_type_assignment(env.type_mapping)
        if e.atomic():
            return e.copy()
        elif e.__class__ in pure_ops:
            return e.copy_local(*[extract_boolean_r(subexpr) for subexpr in e])
        elif e in mapped:
            # note: syntactic equivalence only!
            return mapped[e]
        else:
            var = fresh()
            mappings[var.op] = e
            mapped[e] = var
            return var
    results = [extract_boolean_r(e.under_type_assignment(env.type_mapping))
                                                                for e in exprs]
    return (results, mappings)


def truthtable(e, max_terms=12, simplify=False, extract=False):
    """
    Calculate a truth-table for expression `e`. If `e` is a purely boolean
    expression (see `is_pure`) this will be a complete truth-table, but
    otherwise it may have unreduced expressions in the result.
    
    This is a brute-force calculation, and so is exponential (time and space)
    in the number of terms, hence the heuristic `max_terms` parameter.
    """
    if simplify:
        e = e.simplify_all()
    a = {}
    if extract:
        e, a = extract_boolean(e)
        e = e[0]
    return Evaluations(e, truthtable_valuations(e, max_terms=max_terms),
                    display_assignment=a)


def truthtable_equiv(e1, e2, simplify=True, max_terms=12):
    """Are e1 and e2 equivalent in terms of evaluation on a truth-table?

    e1 and e2 must be propositional. This supports formulas with complex
    propositional elements, but they will be compared on syntactic equivalence
    only."""
    if simplify:
        e1 = e1.simplify_all()
        e2 = e2.simplify_all()
    result, assignment = extract_boolean(e1, e2)
    # display(truthtable(result[0]), truthtable(result[1]))
    return truthtable(result[0], max_terms=max_terms) == truthtable(result[1],
                        max_terms=max_terms)


def truthtable_valid(e, simplify=True):
    if simplify:
        e = e.simplify_all()
    result, assignment = extract_boolean(e)
    return all((eval[1] == true_term) for eval in truthtable(result[0]))


def truthtable_contradictory(e, simplify=True):
    if simplify:
        e = e.simplify_all()
    result, assignment = extract_boolean(e)
    return all((eval[1] == false_term) for eval in truthtable(result[0]))

