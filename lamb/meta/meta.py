import random
import collections.abc

import lamb
from lamb import types

from . import core, boolean
from lamb import types, parsing
from lamb.utils import ensuremath
from lamb.types import TypeMismatch, type_e, type_t, type_n, BasicType, SetType, TupleType


class OutOfDomain(Exception):
    def __init__(self, f, a):
        self.f = f
        self.a = a

    def __str__(self):
        return f"`{self.a}` missing from function domain (`{repr(self.f.op)}`)"

    def __repr__(self):
        return self.__str__()


class MetaTerm(core.TypedTerm):
    """Term class for storing direct references to underlying objects in a type domain."""
    def __init__(self, name, typ=None, setfun=False):
        type_verified = False
        if isinstance(name, MetaTerm):
            # essentially, copy `name`
            if typ is None:
                typ = name.type
                type_verified = True
            name = name.op

        # though super sets this, for various error cases on the type check it
        # is useful to set it in advance and then rely on it in the type check
        self.op = name
        self.type = None

        if not type_verified:
            typ = self.check_type_domain(typ=typ, setfun=setfun)

        # this is kind of clunky, but enforce various normalized representations
        # from the type domain. E.g. this puts a `_` on atomic string values,
        # wraps dicts/sets with frozendict/frozenset
        # XX normalization is already happening during the type check, can it
        # be reused?
        name = typ.domain.normalize(name)

        super().__init__(name, typ=typ, type_check=False, validate_name=False)
        self._variable = False
        self._constant = True

        # cosmetics: hide the type subscript in rich reprs for t/n
        if self.type == type_t or self.type == type_n:
            self.suppress_type = True

        # not set by superclass with type_check=False
        self._type_env = self.calc_type_env()
        self.assignment_name = None

    def check_type_domain(self, typ=None, setfun=False):
        if typ is None:
            # try to infer the type from self.op
            typ = core.get_type_system().get_element_type(self.op, setfun=setfun)
            if typ is None:
                raise parsing.ParseError(
                            f"Unknown type domain element: `{self.op_repr()}`")
            return typ
        else:
            if self.op not in typ.domain:
                if typ.bound_type_vars():
                    # it's helpful to have a specific error for this case
                    raise TypeMismatch(value, typ,
                        error=f"Can't instantiate domain elements with variable types")
                else:
                    raise TypeMismatch(self.op, typ,
                        error=f"Invalid element reference for type domain of `{typ}` in term: `{self.op_repr()}`")
            if isinstance(typ, types.DisjunctiveType):
                # always fully resolve a disjunctive type if it is provided to
                # this function
                dtyp = typ.resolve_element_type(self.op)
                if dtyp is None:
                    # shouldn't be possible...
                    raise TypeMismatch(self.op, typ,
                        error="failed to fully resolve disjunctive type in MetaTerm??")
                typ = dtyp
            # XX it might be possible to handle a type variable here by
            # resolving it as in the `None` case?
            return typ

    def apply(self, arg):
        if not self.type.functional() or not core.get_type_system().eq_check(self.type.left, arg.type):
            raise TypeMismatch(self, arg, error="Function-argument application: mismatched argument type to MetaTerm")
        elif not arg.meta():
            return self(arg)
        elif isinstance(self.op, collections.abc.Set):
            # this will raise if somehow self.type.right is not t
            return MetaTerm(arg in self.op or arg.op in self.op, typ=self.type.right)
        elif isinstance(self.op, collections.abc.Mapping):
            # XX is there a better way to handle this?
            if arg in self.op:
                return MetaTerm(self.op[arg], typ=self.type.right)
            elif arg.op in self.op:
                return MetaTerm(self.op[arg.op], typ=self.type.right)
            else:
                raise OutOfDomain(self, arg)
        else:
            raise ValueError(f"Unknown MetaTerm value `{self.op}`!")

    def meta(self):
        return True

    def copy(self):
        return self.copy_local()

    def copy_local(self, type_check=True):
        r = MetaTerm(self.op, typ=self.type)
        r.latex_op_str = self.latex_op_str
        r.assignment_name = self.assignment_name
        return r

    def under_assignment(self, assignment):
        # ensure that these terms are completely inert to assignments
        return self

    def __bool__(self):
        # TODO: currently `0` converts to False, but perhaps it shouldn't,
        # given that it doesn't compare equal to False, and MetaTerm(0, type_t)
        # gives a TypeMismatch.
        return bool(self.op)

    def __eq__(self, other):
        if other in self.type.domain:
            # compare as equal to domain elements.
            # while this will generally behave symmetrically if the type domain
            # is constructed from python basic types, symmetric behavior can't
            # be assumed in general. If the type domain involves objects that
            # implement __eq__, and you want symmetry, you will have to special
            # case the comparison to a MetaTerm.
            return self.op == other
        elif isinstance(other, core.TypedExpr):
            # note: without the type check, 0 vs False and 1 vs True compare equal,
            # because `bool` is a subtype of `int`
            return other.meta() and self.type == other.type and self.op == other.op
        else:
            # neither a TypedExpr no a python object in the type domain
            return False

    def __hash__(self):
        # overrode __eq__, so also need to override __hash__. We hash with
        # the operator, since dict comparison relies on this.
        if self.op.__hash__:
            return self.op.__hash__()
        else:
            # this will probably raise. Certain python types we allow in `op`,
            # namely dict and set, aren't hashable.
            # TODO: convert to frozenset, and some sort of frozendict implementation?
            return hash(self.op)

    def op_repr(self, rich=False, addsf=False):
        if self.type is None:
            # error in constructor, just need something here
            return str(self.op)
        r = self.type.domain.element_repr(self.op, rich=rich)
        if addsf and rich:
            r = f"\\textsf{{{r}}}"
        return r

    def calc_type_env(self, recalculate=False):
        # currently, MetaTerms are not represented at all in the type
        # environment. They definitely need to be absent from var_mapping, but
        # should they be present in some form?
        return core.TypeEnv()

    def type_env(self, constants=False, target=None, free_only=True):
        return set()

    def free_terms(self, var_only=False):
        return set()

    def __repr__(self):
        return f"{self.op_repr()}_{repr(self.type)}"

    def latex_str(self, show_types=True, assignment=None, use_aname=None, **kwargs):
        # TODO: similar to __repr__, possibly this code should be on the
        # type domain itself
        # if just using `op` as the name, we use textsf, but setting
        # an arbitrary latex name is allowed
        if use_aname is None:
            use_aname = True
        if self.latex_op_str is None:
            if use_aname and self.assignment_name is not None:
                # XX this is a bit ad hoc, could it be better systematized?
                # maybe a piece of the assignment itself should be saved?
                if isinstance(self.assignment_name, tuple):
                    aname, aname2 = self.assignment_name
                else:
                    aname = self.assignment_name
                    aname2 = None
                if isinstance(self.type, BasicType):
                    superscript = self.op_repr(rich=True, addsf=True)
                else:
                    # don't try to show the actual value for this case
                    superscript = "\\text{\\textsf{[meta]}}"
                if aname2:
                    # assumption: aname2 is a str
                    superscript = f"{aname2}/{superscript}"
                return aname.latex_str(show_types=show_types,
                                            assignment=assignment,
                                            superscript=superscript,
                                            **kwargs)
            else:
                # render a domain element name as sans serif
                op_str = self.op_repr(rich=True, addsf=True)
        else:
            # assumption: this is only used in cases where the op string is
            # giving an extremely stable constant name (e.g. \bot for False)
            op_str = f"{self.latex_op_str}"
        if not show_types or not self.should_show_type(assignment=assignment):
            return ensuremath(op_str)
        else:
            # does this need to be in a \text? frontend compat in general...
            return ensuremath(f"{{{op_str}}}_{{{self.type.latex_str()}}}")

    def _repr_latex_(self):
        # override: when directly inspecting an arbitrary MetaTerm, suppress
        # any assignment-derived name, except for the BasicType case, which
        # always shows the value
        return self.latex_str(suppress_parens=True, use_aname=isinstance(self.type, BasicType))

    @classmethod
    def random(cls, random_ctrl_fun, typ=None, blockset=None, usedset=set(),
                            prob_used=0.8, prob_var=0.5, max_type_depth=1):
        # MetaTerm can also be instantiated by TypedTerm.random, and that is
        # the only way that is reachable recursively
        if typ is None:
            typ = random.choice(list(core.get_type_system().atomics))

        if typ not in core.get_type_system().atomics:
            raise TypeMismatch(typ, "Can't randomly instantiate MetaTerm at this type")

        return core.TypedExpr.term_factory(typ.domain.random(), typ)


def is_propositional(e):
    # in principle, could allow type variables here
    return e.type == types.type_t

# TODO: run these with time-based timeouts, rather than heuristic maxes
# TODO: there might be faster ways to do this with numpy arrays + broadcasting

def combinations_gen(l, elems):
    for c in itertools.product(elems, repeat=len(l)):
        yield dict(zip(l, c))

# the following code is essentially calculating
# `list(combinations_gen(terms, elems))`. Unfortunately, doing this the compact
# way is noticeably inefficient. In fact, unfortunately, I haven't
# even been able to get a generator version that is as fast as the following
# code (I guess because of yield overhead?)
#
# >>> s = list('abcdefghijklmnopqrstuv')
# >>> %time x = combos(s, (False, True), max_length=100)
# >>> %time x = list(combinatsion_gen(s, (False, True)))
# CPU times: user 1.04 s, sys: 282 ms, total: 1.32 s
# Wall time: 1.33 s
# CPU times: user 3.65 s, sys: 242 ms, total: 3.89 s
# Wall time: 3.97 s

# warning, exponential in both time and space in the size of `terms`...
def combinations(terms, elems, max_length=20):
    # 20 here is somewhat arbitrary: it's about where exponential blowup gets
    # noticeable on a reasonably fast computer with two elems
    # XX should factor in elems
    if len(terms) > max_length:
        raise ValueError(f"Tried to calculate combinations for an overlong sequence: {repr(terms)}")
    if not elems:
        raise ValueError("Can't produce value combinations without elements")
    if not terms:
        return [{}]
    if len(elems) == 1:
        # this case is very simple, return early
        return {t: elems[0] for t in terms}
    stop = len(terms) - 1
    elem_range = range(len(elems) - 2)
    # now we can assume 2+ elems
    last_elem = elems[-1]
    last2_elem = elems[-2]
    g = []
    def combos_r(i, accum):
        if elem_range:
            for j in elem_range:
                branch = accum.copy()
                branch[terms[i]] = elems[j]
                if i < stop:
                    combos_r(i + 1, branch)
                else:
                    g.append(branch)
        # unroll two iterations. Doing this gets a non-trivial speedup for
        # large term lists, partly from the unrolling, partly from not copying
        # for the last accum, and partly from the precalculation of the element
        # values rather than accessing from elems. Doing this is essentialy an
        # optimization for the boolean case.
        branch = accum.copy()
        branch[terms[i]] = last2_elem
        accum[terms[i]] = last_elem
        if i < stop:
            combos_r(i + 1, branch)
            combos_r(i + 1, accum)
        else:
            g.append(branch)
            g.append(accum)

    combos_r(0, dict())
    return g


def all_boolean_combos(l, cur=None, max_length=20):
    return combinations(l, (False, True), max_length=max_length)


def sorted_term_names(e, var_map = None):
    if var_map is None:
        var_map = e.get_type_env().var_mapping
    terms = list(var_map.keys())
    # TODO: better sort orders?
    terms.sort()
    return terms


def truthtable_repr(t):
    # this is maybe a bit misleading to use, since `0` and `1` in the
    # metalanguage are not convertable to False/True. But I find these
    # the most readable symbols to use in a truth-table.
    if t == False:
        return 0
    if t == True:
        return 1
    try:
        return t._repr_latex_()
    except AttributeError:
        return t


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
        self.term_exprs = [core.term(t, typ=var_map[t]) for t in self.terms]
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
        
        def tname(v, t):
            if t in v:
                return truthtable_repr(v[t])
            else:
                return ""

        for row in self:
            v, result = row
            rows.append(
                [f"| {tname(v, t)}" for t in self.get_valued_terms()]
                + [f"| {truthtable_repr(result)}"])

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
    env = core.TypeEnv()
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
        return core.term(name, typ=types.type_t)

    def extract_boolean_r(e):
        nonlocal mappings
        e = e.under_type_assignment(env.type_mapping)
        if e.atomic():
            return e.copy()
        elif e.__class__ in boolean.pure_ops:
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
        e = e.simplify_all(reduce=True)
    a = {}
    if extract:
        e, a = extract_boolean(e)
        e = e[0]
    return Evaluations(e, truthtable_valuations(e, max_terms=max_terms),
                    display_assignment=a)


def truthtable_equiv(e1, e2, simplify=True):
    """Are e1 and e2 equivalent in terms of evaluation on a truth-table?

    e1 and e2 must be propositional. This supports formulas with complex
    propositional elements, but they will be compared on syntactic equivalence
    only."""

    return truthtable_valid(e1.equivalent_to(e2), simplify=simplify)


def truthtable_valid(e, simplify=True):
    if simplify:
        e = e.simplify_all(reduce=True)
    result, assignment = extract_boolean(e)
    # display(truthtable(result[0]))
    return all((eval[1] == True) for eval in truthtable(result[0]))


def truthtable_contradictory(e, simplify=True):
    if simplify:
        e = e.simplify_all(reduce=True)
    result, assignment = extract_boolean(e)
    return all((eval[1] == False) for eval in truthtable(result[0]))

