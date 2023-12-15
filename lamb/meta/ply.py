from numbers import Number
import re

from lamb import display, types, utils
from lamb.types import TypeMismatch

# code for manipulation and normalization of TypedExprs.
# this is imported by .core


_base_default_sopts = dict(
    reduce=False,
    evaluate=True,
    alphanorm=True, # XX enum?
    collect=True,
    eliminate_sets=False,
    eliminate_quantifiers=False,
    )


def reset_sopts():
    global default_sopts
    default_sopts = _base_default_sopts.copy()


default_sopts = {}
reset_sopts()


def get_sopt(opt, sopts=None):
    if sopts is None:
        sopts = dict()
    if opt not in default_sopts:
        # could just raise?
        from .core import logger
        logger.warning(f"Unknown simplify option `{opt}`")
    return sopts.get(opt, default_sopts.get(opt, None))


def right_commutative(cls):
    # here for completeness...
    if not isinstance(cls, type):
        cls = cls.__class__
    return (getattr(cls, 'commutative', False)
        or getattr(cls, 'right_commutative', False))


def left_commutative(cls):
    # TODO: would some sort of abc-like strategy be better here?
    if not isinstance(cls, type):
        cls = cls.__class__
    # let commutative = False and left_commutative = True still entail left
    # commutativity.
    return (getattr(cls, 'commutative', False)
        or getattr(cls, 'left_commutative', False))


def commutative(cls):
    if not isinstance(cls, type):
        cls = cls.__class__
    # if commutative is set, ignore left/right
    c = getattr(cls, 'commutative', None)
    if c is not None:
        return c
    return (getattr(cls, 'left_commutative', False)
        and getattr(cls, 'right_commutative', False))


def associative(cls):
    if not isinstance(cls, type):
        cls = cls.__class__
    return getattr(cls, 'associative', False)


def collectable(cls):
    """An expression is collectable if it can be rejoined, and for operator
    expressions, if it is also associative. This function accepts either a
    TypedExpr object or a TypedExpr class object."""
    if not isinstance(cls, type):
        cls = cls.__class__

    # is there overhead for this beyond the first call?
    from .core import SyncatOpExpr, BindingOp

    # this is all a bit heuristic...really for any O where the operator's argument
    # type requirements are consistent with its output, we should be able to
    # collect...
    return ((issubclass(cls, SyncatOpExpr) and cls.arity > 1 and associative(cls)
                # if a binding op *can* recurse, it is collectable (e.g.
                # SetContains and the like simply can't recurse...)
                # XX is there a possible binding op where this would be false?
                or issubclass(cls, BindingOp)
                or getattr(cls, 'collectable', False) # custom hook
                )
            and getattr(cls, 'join', None))


def collect(e):
    """Collect expressions into n-ary lists where possible. In particular, an
    associative operator (like &, |) is collected into a complete list of
    conjoined/disjoined expressions, and a binding operator is collected into
    a sequence of variables plus a final value. A non-collectable expression
    will be returned as the class value plus a singleton list.

    Returns
    -------
    A tuple consisting of class, and and a possibly singleton list of
    sub-elements. Guarantees: `(join(*collect(e))) == e`. (Though note that this
    call sequence will rebuild a collectable expression, not copy it!)
    """
    cls = e.__class__
    c = []
    def collect_r(e):
        if not isinstance(e, cls) or not collectable(cls):
            c.append(e)
        else:
            for sub in e:
                collect_r(sub)
    collect_r(e)
    return cls, c

def join(cls, es, empty=None):
    if collectable(cls): # ensures the existence of `join` #getattr(cls, 'join', None):
        return cls.join(es, empty=empty)
    elif len(es) == 1:
        # ignore the class value, no copying
        return es[0]
    else:
        # shouldn't be reachable from anything produced by `collect`
        raise NotImplementedError(f"Don't know how to join `{repr(es)}`")

def op_key(e):
    # should this just use class?
    if isinstance(e.op, str):
        return e.op
    else:
        return repr(e.op)

def alphanorm_key(e):
    # decorate an expression into a tuple for sort purposes
    from .core import SyncatOpExpr
    from .sets import ListedSet # is there a way of implementing this on the subclass?
    if e.meta():
        # order: metaterms, terms, complex terms
        # ' ' precedes all other alphanumeric ascii symbols
        if isinstance(e.op, Number):
            # use the op directly for numeric, not lexicographic sort. To
            # avoid an exception, we use a different (unique) decoration
            # for numbers, so that numbers can never be compared with str
            return (' #', e.op)
        else:
            # tbd if this generally results in sane sort orders
            return (' 0', repr(e))
    elif e.term():
        return (' 1', repr(e))
    elif isinstance(e, SyncatOpExpr) and e.arity == 1:
        # special case: sort negated expressions with their positive
        # forms. This is written in a general way, but it currently
        # only impacts logical negation, and unary negation with variables.
        # (Unary negated metaterms are always pre-simplified into MetaTerms
        # with a negative value.)
        sub = alphanorm_key(e[0])
        return sub + (op_key(e),)
    elif isinstance(e, ListedSet):
        # sort by first cardinality, then repr
        return (op_key(e), len(e)) + tuple(repr(a) for a in collect(e)[1])
    else:
        # type?
        # this could recurse...
        return (op_key(e), ) + tuple(repr(a) for a in collect(e)[1])


def alphanorm_collected(cls, c):
    if len(c) > 1:
        if commutative(cls):
            if associative(cls):
                # commutative + associative = fully reorderable
                # otherwise, sort everything that can be sorted
                c.sort(key=alphanorm_key)
            # XX if something is fully commutative but not associative, no
            # behavior. This should presumably sort 
        elif left_commutative(cls):
            # XX this relies `collect` not generally targeting this property.
            # if there were a left commutative-only operator that had well-formed
            # left recursion, this would do the wrong thing.
            if len(c) > 2:
                # for a left commutative class (e.g. a binding operator) only
                # reorder non-final elements (e.g. variables)
                c[:-1] = sorted(c[:-1], key=alphanorm_key)
        elif right_commutative(cls):
            # this is unused, I just couldn't bear to implement only one
            # direction...
            if len(c) > 2:
                c[1:] = sorted(c[1:], key=alphanorm_key)
    # side effect only: no return


def simplify_all(e, **sopts):
    return e.simplify_all(**sopts)


def multisimplify(e, simplify_fun = None,
                     early_check=None,
                     ctrl=None,
                     **sopts):
    """Simplify a potentially n-ary expression `e`, collecting subexpressions
    (if associative) and potentially doing alphabetic normalization."""

    # this function has to do some relatively involved footwork to track
    # derivations (otherwise, it's not really all that sophisticated)
    cls, es = collect(e)
    orig_len = len(es)

    # for inputs of length 2, showing the collect + join steps are a bit
    # wordy, so reconstruct a conjunction at each step. Could in principle
    # do this always...
    def intermediate(es):
        if orig_len > 2:
            return list(es)
        else:
            return join(cls, es)

    if get_sopt('alphanorm', sopts):
        alphanorm_collected(cls, es)
        initial_reason = f"alphabetic normalization"
    else:
        initial_reason = f"collect"

    derivation = Derivation(origin=e)
    first_step = len(derivation)

    # note: `initial_deriv_trivial` is tracking both sorting *and* associativity
    # changes due to the `collect` call
    initial_deriv_trivial = e == join(cls, es) # this is a bit unfortunate

    if not initial_deriv_trivial:
        derivation.add_step(DerivationStep(intermediate(es),
                desc=initial_reason))

    # note: `pre` should be handled by the caller...    
    # if a control function is supplied, use it to recurse on each individual
    # expression
    if ctrl:
        for i in range(len(es)):
            old = es[i]
            es[i] = ctrl(es[i], **sopts)
            # note: an `is` check is unfortunately not reliable here...
            if old != es[i]:
                desc = ""
                if es[i].derivation and len(es[i].derivation) > 1:
                    desc = f"Recursive simplification of subexpression {i}"
                derivation.add_step(DerivationStep(intermediate(es),
                            desc=desc,
                            subexpression=es[i]))
                if len(es) > 5 and es[i].derivation:
                    # don't collapse the step when showing a `trace()`.
                    # 5 is very heuristic...
                    es[i].derivation.force_on_recurse = True

    # now simplify the multi-expression itself. This currently can *only*
    # handle associative operators, and has no behavior for the non-associative
    # case (e.g. binding operators).
    if associative(e):
        i = 0
        # now, go through pairs of expressions in `es`, applying the simplify
        # function. We rely on normalization to move relevant expressions adjacent
        # to each other. (Could consider more interesting graph-based tricks here...)
        while i < len(es) - 1:
            # if an early stopping check is provided, try it. (E.g. & should stop
            # immediately if it ever finds `False`.)
            if early_check:
                early = early_check(es[i], es[i+1], **sopts)
                if early is not None:
                    tmp_d = early.derivation
                    early.derivation = derivation
                    if tmp_d:
                        derivation.add_step(DerivationStep(early,
                                                desc=tmp_d[-1].desc,
                                                latex_desc=tmp_d[-1].latex_desc))
                    return early
            if simplify_fun:
                step = simplify_fun(es[i], es[i + 1], **sopts)
            else:
                step = None

            if step is None:
                i += 1
                continue
            else:
                es[i] = step
                del es[i + 1]
                derivation.add_step(DerivationStep(intermediate(es), subexpression=step))
                if len(es) > 2 and step.derivation:
                    # don't collapse the step when showing a `trace()`
                    step.derivation.force_on_recurse = True
                if i > 0:
                    i -= 1
    result = join(cls, es)

    need_join_step = orig_len > 2
    if len(derivation) == first_step:
        # no derivation steps added by simplify calls. This can happen either
        # if there were no changes, or the simplify calls don't implement
        # derivational history
        need_join_step = False
    elif len(derivation) == first_step + 1 and not initial_deriv_trivial:
        # only change to be shown is from collect/alphanorm, so collapse the
        # collect and join steps
        derivation[-1].result = result
        need_join_step = False

    if need_join_step:
        # XX does this work for all relevant classes?
        symbol = cls.op_name_uni and cls.op_name_uni or cls.canonical_name
        derivation.add_step(DerivationStep(result, desc=f"join on {symbol}"))
    
    if len(derivation) == 0:
        # no non-trivial derivational steps at all, just wipe the object
        derivation = None
    result.derivation = derivation
    return result


def alphanorm(e):
    # default args = only collect
    return multisimplify(e, alphanorm=True)



###############
#
# Reduction code
#
###############


def unsafe_variables(fun, arg):
    """For a function and an argument, return the set of variables that are not
    safe to use in application."""
    v = arg.free_variables() | fun.free_variables()
    from .core import LFun
    # the actual bound variable is always safe. This check in principle makes
    # this code heavier, but generally prevents a bunch of unnecessary copying
    # for common cases.
    if isinstance(fun, LFun):
        v.discard(fun[0].op)
    return v


def beta_reduce_ts(t, varname, subst):
    from .core import LFun
    if varname in t.free_variables():
        if (t.term() and t.op == varname):
            t = subst.copy()
            t._reduced_cache = subst._reduced_cache.copy()
            return t
        # we will be changing something in this expression, but not at this
        # level of recursion.
        rcache = t._reduced_cache
        parts = [beta_reduce_ts(p, varname, subst) for p in t]
        t = t.copy_local(*parts)
        # update the chart. In particular, beta reduction may create a new
        # subreducible expression by substituting a lambda expression, or an
        # arbitrary subreducible expression, into a function-argument expression
        # that was not previous reducible.
        # example (setup, no chart update): `(L f_<e,e> : f(x))(L x_e : x)`
        #  * the chart for `f(x)` will be [True, True] if it is filled in, but
        #    after substitution, it becomes (L x_e : x)(x), which is not reduced.
        # example (easy): `(L f_<e,e> : f(f(x)))(L x_e : x)`
        #  * the chart for `f(f(x))` will be [True, True] if it is filled in, but
        #    after substitution, it becomes (L x_e : x)(L x_e : x)(x), which
        #    needs the chart [True, False] -- (L x_e : x)(x) is unreduced.
        # example (worse): `((L f_<e,e> : f)((L f_<e,e> : f)((L f_<e,e> : f)(L x_e : x))))(x_e)`
        # example (worse): `(L f_<e,e> : f(f(x_e)))((L f_<e,e> : f)(L x_e : x))`
        #  * the chart for `f(f(x))` if filled in would be [True, True].
        #    after one substitution, we get:
        #    `(λ f_<e,e>: f)(λ x_e: x)((λ f_<e,e>: f)(λ x_e: x)(x_e))`
        #    which should now have [False, False[False, True]]
        # (etc)

        # conditional chart modification. These are exactly the two cases where
        # an existing `True` in the chart may need to be revised. Note that
        # the subreducible() call forces the chart for `subst` to be at least
        # partialy filled in.
        if isinstance(subst, LFun) or subst.subreducible() is not None:
            for i in range(len(rcache)):
                if (rcache[i] == False # unchanged, reduction won't cause a subreduction
                        # checks t[i].reducible():
                        or t[i]._is_reduced_caching() == False):
                    t._reduced_cache[i] = False
                else:
                    t._reduced_cache[i] = rcache[i]
        else:
            t._reduced_cache = rcache.copy()

    return t

def variable_replace(expr, m):
    # unused
    from .core import TypedExpr
    def transform(e):
        return TypedExpr.factory(m[e.op])
    return variable_transform(expr, m.keys(), transform)

def variable_replace_strict(expr, m):
    # unused
    from .core import TypedExpr
    def transform(e):
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            raise TypeMismatch(e, result,
                error="Strict variable replace failed with mismatched types")
        return result
    return variable_transform(expr, m.keys(), transform)

def term_replace_unify(expr, m):
    from .core import TypedExpr, ts_unify_with
    def transform(e):
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            # note: error reporting from here has a different order than the
            # raise below, so we handle it manually... (unclear to me if this
            # is important)
            unify = ts_unify_with(result, e, error=None)
            if unify is None:
                raise TypeMismatch(e, result,
                        error="Variable replace failed with mismatched types")
            if unify == e.type: # unify gives us back e.  Can we return e?
                if result.term() and result.op == e.op:
                    return e
                else:
                    return result
            elif unify == result.type: # unify consistent with result
                return result
            else: # unify results in a 3rd type
                result = result.try_adjust_type(unify, assignment=m)
                return result
        else:
            if result.term() and result.op == e.op:
                return e
            else:
                return result

    r = term_transform_rebuild(expr, m.keys(), transform)
    return r

def variable_convert(expr, m):
    from .core import TypedTerm
    def transform(e):
        return TypedTerm(m[e.op], e.type)
    return variable_transform(expr, m.keys(), transform)

def variable_transform(expr, dom, fun):
    """Transform free instances of variables in expr, as determined by the
    function fun.

    Operates on a copy.
    expr: a TypedExpr
    dom: a set of variable names
    fun: a function from terms to TypedExprs."""
    # TODO: check for properly named variables?
    # TODO: double check -- what if I recurse into a region where a variable
    # becomes free again??  I think this goes wrong
    targets = dom & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be transformed.
            return fun(expr)
        expr = expr.copy()
        for i in range(len(expr.args)):
            expr.args[i] = variable_transform(expr.args[i], dom, fun)
    return expr

def term_transform_rebuild(expr, dom, fun):
    """Transform free instances of variables in expr, as determined by the
    function fun.

    Operates on a copy.
    expr: a TypedExpr
    dom: a set of variable names
    fun: a function from terms to TypedExprs."""

    targets = dom & expr.free_terms()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be transformed.
            return fun(expr)
        seq = list()
        dirty = False
        for i in range(len(expr.args)):
            seq.append(term_transform_rebuild(expr.args[i], targets, fun))
            if seq[-1] != expr.args[i]:
                dirty = True
        if dirty:
            expr = expr.copy_local(*seq)
    return expr


# TODO: these last two functions are very similar, make an abstracted version?

def alpha_variant(x, blockset):
    """find a simple variant of string x that isn't in blocklist.  Try adding
    numbers to the end, basically.
    side effect WARNING: updates blocklist itself to include the new
    variable."""
    if not x in blockset:
        return x
    split = utils.vname_split(x)
    if len(split[1]) == 0:
        count = 1
    else:
        # TODO: double check this -- supposed to prevent counterintuitive things
        # like blocked "a01" resulting in "a1"
        count = int(split[1]) + 1
    prefix = split[0]
    t = prefix + str(count)
    while t in blockset:
        count += 1
        t = prefix + str(count)
    blockset.add(t) # note: fails for non-sets
    return t


def alpha_convert_r(t, overlap, conversions):
    overlap = overlap & t.bound_variables()
    if overlap:
        from .core import BindingOp
        if isinstance(t, BindingOp) and t.varname in overlap:
            # the operator is binding variables in the overlap set.
            # rename instances of this variable that are free in the body of the
            # operator expression.
            t = t.alpha_convert(conversions[t.varname])
        parts = list()
        for i in range(len(t.args)):
            parts.append(alpha_convert_r(t.args[i], overlap, conversions))
        t = t.copy_local(*parts)
    return t


def alpha_convert(t, blocklist):
    """ produce an alphabetic variant of t that is guaranteed not to have any
    variables in blocklist.  

    Possibly will not change t."""
    overlap = t.bound_variables() & blocklist
    if not overlap:
        return t
    full_bl = blocklist | t.free_variables() | t.bound_variables()
    # note that this relies on the side effect of alpha_variant...
    conversions = {x : alpha_variant(x, full_bl) for x in overlap}
    return alpha_convert_r(t, overlap, conversions)


# XX overlap with parsing code...
# XX maybe too strict for initial char depending on locale?
symbol_re = re.compile(r'^[a-zA-Z_]\w*$')
var_re = re.compile(r'^[a-z]\w*$')


def is_symbol(s):
    """A string `s` is a symbol if it starts with an alphabetic char or `_` and
    contains only alphanumeric characters."""
    return isinstance(s, str) and bool(re.match(symbol_re, s))


def symbol_is_var_symbol(s):
    return s[0].islower()


def is_var_symbol(s):
    """A string s is a variable symbol if it's a symbol that starts with a
    lowercase letter."""
    return isinstance(s, str) and bool(re.match(var_re, s))


#################################
# Derivations


class DerivationStep(object):
    """A single step of a derivation."""
    def __init__(self, result,  desc=None, origin=None, latex_desc=None,
                                        subexpression=None, trivial=False):
        self.result = result
        self.subexpression = subexpression
        if desc is None:
            if latex_desc is None:
                self.desc = self.latex_desc = ""
            else:
                self.desc = latex_desc
        else:
            self.desc = desc
            if latex_desc is None:
                self.latex_desc = desc
            else:
                self.latex_desc = latex_desc
        self.set_origin(origin)
        self.trivial = trivial

    def set_origin(self, origin):
        from .core import is_te
        # XX is the >1 case actually used
        if origin is None:
            self.origin = ()
        elif is_te(origin):
            # prevent sequence handling from splitting a TypedExpr
            self.origin = (origin,)
        else:
            # origin should be an iterable
            self.origin = tuple(origin)

    def get_origin(self):
        # does *not* extract a non-trivial tuple of origins...
        if self.origin:
            return self.origin[0]
        else:
            return None

    def copy(self):
        return DerivationStep(self.result, desc=self.desc, origin=self.origin,
            latex_desc=self.latex_desc, subexpression=self.subexpression,
            trivial=self.trivial)

    def force_on_recurse(self):
        if (self.subexpression is not None
                    and self.subexpression.derivation is not None):
            self.subexpression.derivation.force_on_recurse = True

    def result_str(self, latex=False):
        if latex:
            if self.trivial:
                return "..."
            if isinstance(self.result, list) or isinstance(self.result, tuple):
                # assumption: sequence of typed exprs
                return f"[{', '.join([x.latex_str() for x in self.result])}]"
            return self.result.latex_str(suppress_parens=True)
        else:
            return repr(self.result)

    def desc_str(self, latex=False):
        if latex:
            return self.latex_desc
        else:
            return self.desc

    def unpack_for_display(self, latex=False, all_recursion=False):
        if (not all_recursion
                and self.subexpression is not None and self.subexpression.derivation
                and self.subexpression.derivation.can_collapse()):
            subdesc, subsubexp = self.subexpression.derivation.collapsed_desc(latex=latex)
            return (self.result_str(latex=latex), subdesc, subsubexp)
            # return (self.result_str(latex=latex), subdesc, self.subexpression)
        return (self.result_str(latex=latex), self.desc_str(latex=latex), self.subexpression)

    def origin_str(self, latex=False):
        if len(self.origin) == 1:
            if latex:
                return self.origin[0].latex_str(suppress_parens=True)
            else:
                return repr(self.origin[0])
        else:
            if len(self.origin) == 0:
                return "???"
            if latex:
                return utils.ensuremath("(" +
                    (" + ".join([o.latex_str() for o in self.origin])) + ")")
            else:
                return "(" + (" + ".join([repr(o) for o in self.origin])) + ")"

    def __repr__(self):
        return ("[DerivationStep origin: "
            + repr(self.origin)
            + ", result: "
            + repr(self.result)
            + ", description: "
            + self.desc
            + "]")

class Derivation(object):
    """A derivation sequence, consisting of DerivationSteps."""

    max_display_steps = 100

    def __init__(self, steps=None, origin=None):
        self.steps = list()
        # note: DerivationStep.origin is a tuple, but here we should be either
        # a TypedExpr or None
        if steps is None and origin is not None:
            steps = origin.derivation # may still be None
        self.origin = origin
        if steps is not None:
            self.add_steps(steps)
            self.result = self[-1] # is this used?
        else:
            self.result = None
        self.force_on_recurse = False

    def last(self):
        if len(self.steps):
            return self.steps[-1].result
        else:
            # may be None
            return self.origin

    def add_step(self, s):
        self.add_steps([s])

    def add_steps(self, steps):
        if not len(self) and self.origin is None and isinstance(steps, Derivation):
            # empty derivation and no origin: copy the origin from `steps`
            self.origin = steps.origin
        if len(steps):
            end = len(self.steps)
            cur_last = self.last()
            self.steps.extend(steps)
            if not self.steps[end].origin:
                self.steps[end].set_origin(cur_last) # may be None
            if end == 0 and self.origin is None:
                # first step(s), still empty origin: copy an origin (if any)
                # out of `steps`
                # XX what does this do if len(s.origin) > 1?
                self.origin = self.steps[0].get_origin()

    def __iter__(self):
        return iter(self.steps)

    def __len__(self):
        return len(self.steps)

    def __getitem__(self, i):
        return self.steps[i]

    def __delitem__(self, i):
        if i + 1 < len(self):
            self.steps[i+1].origin = self.steps[i].origin
        del self.steps[i]

    def can_collapse(self, recursing=True):
        # set `force_on_recurse` to override the default behavior, which will
        # collapse a 1-step sub derivation and show that derivation's reason,
        # even on `trace()`. useful when e.g. simplifying a long sequence at
        # once. A non-recursive derivation will still use a collapsed reason
        # for this case.
        return len(self) == 1 and (not recursing or not self.force_on_recurse)

    def collapsed_desc(self, latex=False):
        # description to use when showing as a collapsed step, overriding
        # self.desc
        if len(self) == 0:
            return None
        _, subdesc, subexp = self[-1].unpack_for_display(latex=latex)
        # this notation may be a bit opaque, is there a better option that
        # is still compact?
        return f"[{subdesc}]", subexp

    def steps_sequence(self, index=None, latex=False, ignore_trivial=False, all_recursion=False):
        l = list()
        if index is None:
            start = None
            stop = None
            # index = slice(0, len(self.steps))
        elif isinstance(index, int):
            start = index
            stop = index + 1
            # index = slice(index, index + 1)
        else:
            start = index.start
            stop = index.stop
        if start is None:
            start = 0
        if stop is None:
            stop = len(self.steps)

        if start < 0 or stop < 0:
            raise ValueError("Negative indexing on derivation displays is not supported")
        trimmed = False
        requested_stop = min(len(self.steps) - 1, stop)
        # TODO: some kind of recursion cap also
        if stop - start > self.max_display_steps - 2:
            stop = start + self.max_display_steps - 1
            trimmed = True
        index = slice(start, stop)
        subselect = self.steps[index]
        # XX include step number here, not in display code?
        if len(subselect) > 0:
            l.append((subselect[0].origin_str(latex), None, None))
            for i in range(len(subselect)):
                # assume that origin matches previous result.  Could check this.
                if subselect[i].trivial and ignore_trivial:
                    continue
                l.append(subselect[i].unpack_for_display(latex=latex, all_recursion=all_recursion))
        if trimmed:
            l.append((f"... {requested_stop - index.stop} steps omitted ...", "", None))
            l.append(self.steps[requested_stop].unpack_for_display(
                                            latex=latex,
                                            all_recursion=all_recursion))
        return l

    def equality_display(self, content, style=None):
        # TODO: small step count cap for this
        l = self.steps_sequence(latex=True, ignore_trivial=True)
        n = display.DisplayNode(content=content, parts=[step[0] for step in l],
                                style = display.EqualityDisplay())
        return n

    def build_display_tree(self, index=None, recurse=False, parent=None,
                                reason=None, all_recursion=False, style=None):
        if all_recursion:
            recurse = True
        defaultstyle = {"align": "left"}
        style = display.merge_styles(style, defaultstyle)
        if index is None:
            index = slice(0, len(self.steps))
        elif isinstance(index, int):
            index = slice(index, index + 1)

        node_style = display.LRDerivationDisplay(start=index.start, **style)
        l = self.steps_sequence(index=index, latex=True, all_recursion=all_recursion)
        parts = list()
        for (expr, subreason, subexpression) in l:
            if reason == "":
                reason = None
            if recurse and subexpression is not None and subexpression.derivation:
                parts.append(subexpression.derivation.build_display_tree(
                        recurse=recurse,
                        parent=expr,
                        reason=subreason,
                        style=style,
                        all_recursion=all_recursion))
            else:
                # given a blank subreason, and 1-step sub-derivation, try
                # importing the subsubreason for display
                if (not subreason and subexpression is not None
                        and subexpression.derivation
                        and subexpression.derivation.can_collapse(recursing=False)):
                    subreason, _ = subexpression.derivation.collapsed_desc(latex=True)

                parts.append(display.DisplayNode(content=expr,
                        explanation=subreason, parts=None, style=node_style))
        if len(parts) == 0:
            parts = None
        return display.DisplayNode(content=parent, explanation=reason,
                                                parts=parts, style=node_style)

    def trace(self, index=None, recurse=True, style=None, all_recursion=False):
        return self.build_display_tree(index=index, recurse=recurse, style=style, all_recursion=all_recursion)

    def show(self, index=None, recurse=False, style=None, all_recursion=False):
        return self.trace(index=index, recurse=recurse, style=style, all_recursion=all_recursion)

    def _repr_html_(self):
        return self.build_display_tree(recurse=False)._repr_html_()

    def steps_str(self):
        # XX _repr_pretty_, could implement trace() for text output as well
        l = self.steps_sequence(latex=False)
        s = ""
        i = 1
        for (expr, reason, subexpression) in l:
            if (not reason and subexpression is not None
                    and subexpression.derivation
                    and subexpression.derivation.can_collapse(recursing=False)):
                reason, _ = subexpression.derivation.collapsed_desc(latex=False)

            if not reason:
                s += "%2i. %s\n" % (i, expr)
            else:
                # XX align reasons
                s += "%2i. %s    (%s)\n" % (i, expr, reason)
            i += 1
        return s

    def __repr__(self):
        return self.steps_str()


def derivation_factory(result, desc=None, latex_desc=None, origin=None,
                                steps=None, subexpression=None, trivial=False):
    """Convenience factory function for `Derivation`s, that populates it with
    an initial step determined by the parameters."""
    drv = Derivation(steps)
    # note: will make a copy of the derivation if steps is one; may be better to have something more efficient in the long run
    drv.add_step(DerivationStep(result, desc=desc, origin=origin,
                latex_desc=latex_desc, subexpression=subexpression, trivial=trivial))
    return drv

def derived(result, origin, desc=None, latex_desc=None, subexpression=None,
                                                        allow_trivial=False,
                                                        force_on_recurse=False):
    """Convenience function to return a derived TypedExpr while adding a
    derivational step. Always return result, adds or updates its derivational
    history as a side effect."""

    from .core import TypedTerm # can these be done without isinstance checks?
    from .meta import MetaTerm
    if isinstance(result, MetaTerm) and result.derivation is None:
        result = result.copy()
    elif isinstance(result, TypedTerm) and result.derivation is None:
        try:
            # need to manually copy the typeenv??  TODO: double check...
            tenv = result._type_env
            # avoid mixing up derivations on terms.  TODO: how bad is this?
            result = result.copy()
            result._type_env = tenv
        except AttributeError: # no _type_env set
            result = result.copy()
    trivial = False
    if result == origin: # may be inefficient?
        if allow_trivial:
            trivial = True
        else:
            # a bit hacky, but this scenario has come up
            if result.derivation is None and result is not origin:
                result.derivation = origin.derivation
            return result
    if result.derivation is None:
        d = origin.derivation
    else:
        d = result.derivation
    result.derivation = derivation_factory(result, desc=desc,
                                                   latex_desc=latex_desc,
                                                   origin=origin,
                                                   steps=d,
                                                   subexpression=subexpression,
                                                   trivial=trivial)
    if force_on_recurse:
        result.derivation[-1].force_on_recurse()
    return result

def add_derivation_step(te, result, origin, desc=None, latex_desc=None,
                                    subexpression=None, allow_trivial=False):
    trivial = False
    if result == origin: # may be inefficient?
        if allow_trivial:
            trivial = True
        else:
            return te
    if te.derivation is None:
        d = origin.derivation
    else:
        d = te.derivation
    te.derivation = derivation_factory(result, desc=desc,
                                               latex_desc=latex_desc,
                                               origin=origin,
                                               steps=d,
                                               subexpression=subexpression,
                                               trivial=trivial)
    return te

def add_subexpression_step(te, subexpr, desc=None, latex_desc=None):
    if subexpr.derivation is None or len(subexpr.derivation) == 0:
        return te
    start = subexpr.derivation[0].origin[0]
    end = subexpr.derivation[-1].origin[-1]
    add_derivation_step(te, end, start, desc=desc, latex_desc=latex_desc,
                                                        subexpression=subexpr)
    return te

