import sys, re, logging, random, functools, inspect, operator
import collections, contextlib
from numbers import Number
from dataclasses import dataclass

import lamb
from lamb import types, parsing, utils
from lamb.utils import ensuremath, dbg_print, Namespace

from lamb.types import TypeMismatch, BasicType, FunType, TupleType, is_type_var
# meta.ply and meta.parsing are the only meta modules imported by core
from .parser import find_term_locations, parse_term, try_parse_term_sequence
from .parser import base_term_re, try_parse_typed_term
from .ply import derived, collectable, multisimplify, alphanorm, get_sopt
from .ply import simplify_all, symbol_is_var_symbol, alphanorm_key
from .ply import is_var_symbol, is_symbol, unsafe_variables, alpha_convert, beta_reduce_ts
from .ply import term_replace_unify, variable_convert, alpha_variant
from .ply import commutative, associative, left_commutative, right_commutative
from .ply import Derivation, DerivationStep, set_derivation, no_derivations

############### Basic stuff

global logger
def setup_logger():
    """Set up a module-level logger called `logger` for use across `lamb`
    modules."""
    global logger
    logger = logging.getLogger("lamb")
    logger.handlers = list() # otherwise, will get double output on reload
                             # (since this just keeps adding handlers)
    logger.setLevel(logging.INFO)
    logger.propagate = False
    # note that basicConfig does _not_ work for interactive ipython sessions,
    # including notebook.
    infoch = logging.StreamHandler(sys.stdout)
    infoch.setFormatter(logging.Formatter(
                                '%(levelname)s (%(module)s): %(message)s'))
    def info_filter(record):
        if record.levelno == logging.INFO:
            return 1
        else:
            return 0
    infoch.addFilter(info_filter)
    infoch.setLevel(logging.INFO)

    errch = logging.StreamHandler(sys.stderr)
    #ch.setLevel(logging.INFO)
    errch.setLevel(logging.WARNING)
    errch.setFormatter(logging.Formatter(
                                '%(levelname)s (%(module)s): %(message)s'))
    logger.addHandler(errch)
    logger.addHandler(infoch)


setup_logger()


global _constants_use_custom, _type_system, _allow_coerced_types, _allow_guessed_types
_constants_use_custom = False
_allow_coerced_types = True
_allow_guessed_types = True


def constants_use_custom(v):
    """Set whether constants use custom display routines."""
    global _constants_use_custom
    _constants_use_custom = v


def set_strict_type_parsing(strict=True, coerced=None):
    global _allow_coerced_types, _allow_guessed_types
    if coerced is None:
        coerced = strict
    _allow_guessed_types = not strict
    _allow_coerced_types = not coerced


# this will leave _type_system as None if something crashes in setup
_type_system = None
registry = None
_namespace = {}

def global_namespace():
    global _namespace
    return _namespace


# TODO: could consider associating TypedExpr with a type system rather than
# using the global variable. advantages: generality.  Disadvantages: may be a
# little pointless in practice?
def set_type_system(ts):
    """Sets the current type system for the metalanguage.  This is a global
    setting."""
    global _type_system
    _type_system = ts


def reset_type_system():
    global _type_system
    types.reset()
    _type_system = types.poly_system


def get_type_system():
    """Gets the current (global) type system for the metalanguage."""
    return _type_system


def ts_unify(a, b):
    """Calls the current type system's `unify` function on types `a` and `b`.
    This returns a unified type, or `None` if the two can't be unified."""
    return get_type_system().unify(a, b)


def ts_reconcile(a, b, error=None):
    if error is True:
        error = f"Failed to reconcile types"
    if a is None:
        if error and b is None:
            # Or, TypeMismatch?
            raise ValueError("No type provided for `ts_reconcile`")
        return b
    elif b is None:
        return a
    else:
        r = ts_unify(a, b)
        if r is not None or not error:
            return r
        else:
            raise TypeMismatch(a, b, error)


def ts_unify_with(a, b, error=None):
    """Try to unify the types of expressions `a` and `b`. This does not change
    the expressions themselves at all, but they are used for error reporting.
    On failure, this may either return None or raise a TypeMismatch. If
    `error` is set, guarantees a TypeMismatch on failure; otherwise, the caller
    should handle error conditions. The value of `error` may be overridden
    by the type system.
    """
    try:
        # for the most part, the type system won't actually raise. The case
        # where it does is occurs check failures.
        result = get_type_system().unify(a.type, b.type, allow_raise=True)
        # an exception from the `unify` call will override `error`
        if result is None and error is not None:
            raise TypeMismatch(a.type, b.type, error=error)
        return result
    except TypeMismatch as e:
        # sub in the provided expressions on `e`. e.type1 and e.type2 should
        # already be set...though we aren't guaranteed that they correspond
        # to the expressions.
        e.i1 = a
        e.i2 = b
        raise e


global unify
unify = ts_unify # remove this?

def ts_compatible(a, b):
    """Returns `True` or `False` depending on whether `a` and `b` are
    compatible types."""
    ts = get_type_system()
    return ts.unify(a,b) is not None

def tp(s):
    """Convenience wrapper for the current type system's type parser."""
    return get_type_system().type_parser(s, require_exact_type=True)

def let_wrapper(s):
    result = derived(s.compact_type_vars(), s, "Let substitution")
    result.let = True
    return result


def tenorm(e):
    if isinstance(e, TypedExprFacade):
        return e._e
    else:
        return e


def tefnorm(e):
    if isinstance(e, TypedExpr):
        return e.M
    else:
        return e


def te(s, *, let=True, assignment=None, _globals=None, fullcopy=True):
    """Public interface for constructing `TypedExpr` objects; `s` may be a
    string, in which case it will be parsed."""

    # XX incorporate lexicon namespace into this function somehow?
    if _globals is None:
        _globals = global_namespace()
    result = tenorm(TypedExpr.factory(s, assignment=assignment,
                                        _globals=_globals, fullcopy=fullcopy))
    if let and isinstance(result, TypedExpr):
        result = let_wrapper(result)
    return result


def is_te(x, cls=None):
    if cls is None:
        return isinstance(x, TypedExpr)
    else:
        return issubclass(cls, TypedExpr) and isinstance(x, cls)


def validate_te(x, s=None):
    if not is_te(x):
        name = getattr(x, '_meta_name_', None)
        if name is not None:
            raise parsing.ParseError(f"Invalid syntax: stray operator `{name}`", s=s)
        else:
            # how to make this less cryptic?
            raise parsing.ParseError(f"Invalid syntax", s=s)
    return x


def is_equality(x):
    # this looks a bit brittle, but this is probably the best current way to
    # check for all equality/equivalence relations at once.
    return x.op == "<=>"


def term(s, typ=None, assignment=None, meta=False):
    """Convenience wrapper for building terms.
    `s`: the term's name.
    `typ`: the term's type, if specified."""
    r = TypedTerm.term_factory(s, typ=typ, assignment=assignment)
    if meta:
        # return only if r is a valid MetaTerm
        if r is None and isinstance(s, TypedExpr) and not s.meta():
            raise parsing.ParseError(f"Failed to infer a type domain element from expression", s=s)
        elif r is None:
            raise types.TypeMismatch(s, typ, f"Failed to infer a type domain element at correct type")
        elif not r.meta():
            raise parsing.ParseError(f"Failed to infer a type domain element", s=s)
    return r


def check_type(item, typ, raise_tm=True, msg=None):
    ts = get_type_system()
    if not ts.eq_check(item.content.type, typ):
        if raise_tm:
            raise types.TypeMismatch(item, typ, error=msg)
        else:
            return None
    else:
        return item


def default_variable_type(s):
    #TODO something better
    return types.type_e

def default_type(s):
    if isinstance(s, TypedExpr):
        return s.type
    elif isinstance(s, bool):
        return types.type_t
    elif types.is_numeric(s):
        return types.type_n
    elif isinstance(s, str):
        t = utils.num_or_str(s)
        if types.is_numeric(s):
            return types.type_n
        elif isinstance(s, bool):
            return types.type_t
        elif is_var_symbol(t):
            return default_variable_type(s)
        else:
            #TODO, better default
            return types.type_t
    else:
        # TODO: more default special cases?  predicates?
        raise NotImplementedError


def let_compact_type_vars(*args, unsafe=None, store_mapping=False, all_vars=False):
    """Compact the type variables on expressions in `args` into X
    variables with a low number. This is primarily intended for
    returning freshened types to a human-readable form. Elements
    in `args` are assumed to have mutually interpretable types, i.e.
    not `let` bound."""
    history_env = [a.get_type_env() for a in args]
    if all(len(e.type_var_set) == 0 for e in history_env):
        if len(args) == 1:
            return args[0]
        else:
            return args
    envs = [a.copy() for a in history_env]
    used_vars = set().union(*[e.used_vars() for e in envs])
    if not all_vars:
        if unsafe is None:
            unsafe = set()
        unsafe = unsafe | set([e for e in used_vars if not e.is_fresh()])
        # compact only fresh vars
        used_vars = [e for e in used_vars if e.is_fresh()]

    compacted_map = types.compact_type_set(used_vars, unsafe=unsafe)
    # `under_type_injection` copies
    results = [a.under_type_injection(compacted_map) for a in args]
    for i in range(len(results)):
        results[i]._type_env_history = history_env[i]
    if not store_mapping:
        for r in results:
            r.get_type_env(force_recalc=True)
    if len(results) == 1:
        return results[0]
    else:
        return results


def let_freshen(*args):
    """Freshen any let-bound types in `args`"""
    lets = [a.let for a in args]
    result = [a for a in args]
    result_let = False
    if any(lets):
        if all(lets):
            # special case: if every element in `args` is let-bound, we can
            # do pretty much what we want with the variables as long as
            # collisions are avoided, and rebind everything. The code here
            # is a little more complicated in order to try to get nicer
            # results that don't replace too many variables.
            freshen = [False] * len(result)
            for i in range(len(freshen)):
                if freshen[i] is True:
                    continue
                for j in range(i, len(freshen)):
                    if (result[i].get_type_env().type_var_set &
                                    result[j].get_type_env().type_var_set):
                        freshen[i] = freshen[j] = True
            # it's always safe to leave one unfreshened, because we will `let`
            # the result. (This could be more sophisticated depending on
            # the actual overlaps)
            for i in range(len(result)):
                if freshen[i]:
                    freshen[i] = False
                    break
            for i in range(len(result)):
                if freshen[i]:
                    result[i] = result[i].freshen_type_vars()
            # if everything is `let`-marked, we should `let` the result
            result_let = True
        else:
            # in this case, we don't know the context, and so must call freshen
            # on everything. (Reminder: this call still checks `let`.)
            for i in range(len(result)):
                # this call checks let
                # XX derivations?
                result[i] = result[i].freshen_type_vars()
    # else: no adjustment to `result`
    return result_let, result


def combine_with_type_envs(fun, *args, **kwargs):
    """Combine some sequence of arguments using `fun`, while handling type
    variables correctly."""
    result_let, inter = let_freshen(*args)
    result = fun(*inter, **kwargs).regularize_type_env()
    if result_let or result.let:
        result = let_wrapper(result)
    return result


class MiniOp(object):
    """This is a class to pass to a TypeMismatch so that the operator is
    displayed nicely."""
    def __init__(self, op_uni, op_latex, typ=None):
        if typ != None:
            self.type = typ
        self.op_uni = op_uni
        self.op_latex = op_latex

    def __repr__(self):
        return self.op_uni

    def __str__(self):
        return repr(self)

    def latex_str(self):
        return self.op_latex

    def short_str_latex(self):
        return self.latex_str()

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def from_op(cls, op):
        return MiniOp(op.op_name, op.op_name_latex)


builtin_arities = {
    '~': {1},
    '-': {1, 2},
    '+': {1, 2},
    '/': {2},
    '//': {2},
    '*': {2},
    '**': {2},
    '%': {2},
    '@': {2},
    '==': {2},
    '!=': {2},
    '<': {2},
    '>': {2},
    '<=': {2},
    '>=': {2},
    '&': {2},
    '|': {2},
    '^': {2},
    '>>': {2},
    '<<': {2}}

# hacky operator aliases. These paper over some inadequacies of pure python
# operators, but are far from a desireable / general solution...
# it is not recommended for end users to mess with this at all
# XX add unicode aliases?
builtin_op_aliases = {
    # do not reorder
    '<=>': '%',
    '==>': '>>', # remove?
    '=>':  '>>', # note: cannot add '<=': '<<' for obvious reasons...
    '<==': '<<', # remove?
    '=/=': '^',
    # note: these intentionally shadow standard python operators! It's not
    # possible to use the standard data model overrides here, because
    # TypedExpr objects must support python equality, and the metalanguage
    # requires that these operators mean equivalence.
    '!=':  '^',
    '==':  '%'
}

def apply_op_aliases(to_eval):
    for k in builtin_op_aliases:
        to_eval = to_eval.replace(k, builtin_op_aliases[k])
    return to_eval

def _sig_to_tuple(typs):
    # replace None with ∀X
    generic = types.VariableType.any()
    return types.TupleType(*[generic if t is None else t for t in typs])

class OperatorRegistry(object):
    class Operator(object):
        def __init__(self, _cls, *targs):
            self.cls = _cls
            self.name = _cls.canonical_name
            self.arity = len(targs)
            # XX can we just use functional types and be done with it? Or at
            # least the tuple only?
            self.targs = targs
            self.arg_signature = types.TupleType(*self.targs)

        def __hash__(self):
            # these checks use only syntactic identity for types; add_operator
            # uses a more general check
            return hash(self.name) ^ hash(self.arity) ^ hash(self.targs)

        def __eq__(self, other):
            return (self.name == other.name
                and self.arity == other.arity
                and self.targs == other.targs)

        def signature_str(self):
            return repr(self.arg_signature)

        @property
        def base_impl(self):
            return getattr(self.cls, 'base_impl', None)

        def __str__(self):
            return f"Operator({self.name}, {self.cls.__name__}, arity: {self.arity}, signature: {self.signature_str()})"

        def __repr__(self):
            if (e := self.base_impl) is not None:
                # use a metalanguage implementation if present
                return f"operator {self.name}({self.arity}) = {repr(e)}"
            else:
                # not a true repr
                return str(self)

        def _repr_latex_(self):
            if (e := self.base_impl) is not None:
                # XX texttt here may not be stable across mathjax/katex versions
                return ensuremath(f'\\texttt{{operator {self.name}({self.arity})}} = {e.latex_str(suppress_parens=True)}')
            else:
                # fall back to plain repr
                return None

        def get_names(self):
            # maybe include unicode?
            r = [self.name]
            if getattr(self.cls, 'secondary_names', None):
                r = r + list(self.cls.secondary_names)
            return r

        def check_types_viable(self, *typs):
            """Return a comparison value with the type of this operator. This
            is not safely convertable to bool! I.e. None is failure, 0 is
            exact match."""
            if self.arity != len(typs):
                return None
            return get_type_system().cmp(
                        types.freshen_type(self.arg_signature),
                        _sig_to_tuple(typs))

        def check_viable(self, *args):
            # if the class has a custom check_viable, defer entirely to that
            # XX currently unused, maybe remove?
            if callable(getattr(self.cls, "check_viable", None)):
                if self.cls.check_viable(*args):
                    return 0
                else:
                    return None

            return self.check_types_viable(*[a.type for a in args])

    def __init__(self):
        self.clear()

    def clear(self):
        self.ops = {}
        self.arities = {}
        self.binding_ops = {}
        self.canonicalize_binding_ops = {}
        self.unparsed_binding_ops = set()
        self.custom_transforms = {}
        self.ordering = {}
        self.exported = set()
        self._term_re = re.compile(base_term_re)

    def add_operator(self, _cls, *targs, shadow_warning=True):
        if not targs and (sig := getattr(_cls, 'arg_signature', None)) is not None:
            targs = sig.signature

        desc = self.Operator(_cls, *targs)
        for symbol in desc.get_names():
            if symbol in builtin_arities and desc.arity not in builtin_arities[symbol]:
                # non-builtins have no validation!
                raise parsing.ParseError(f"Invalid arity ({desc.arity}) for operator `{symbol}`")
            # use dicts and not sets for the sake of ordering
            if not symbol in self.ops:
                self.ops[symbol] = dict()
            warned = None
            if desc in self.ops[symbol]:
                # exact type match, issue a log message
                logger.warning(
                    f"New operator `{desc.name}/{desc.arg_signature}` replaces existing exact matching operator for `{symbol}`: {self.ops[symbol][desc]}")
                self.remove_operator(symbol, self.ops[symbol][desc])
            # check for inexact type matches
            for op in list(self.ops[symbol]):
                if op.check_types_viable(*desc.targs) == 0:
                    # this case is typically guaranteed to be unmatchable, so
                    # remove the existing operator.
                    # XX cases like (e,X) and (Y,e)? Maybe only remove on alpha
                    # equivalents?
                    logger.warning(
                        f"New operator `{desc.name}/{desc.arg_signature}` replaces existing inexact matching operator for `{symbol}`: {op}")
                    self.remove_operator(symbol, op)

            self.ops[symbol][desc] = desc
            if symbol not in self.ordering:
                self.ordering[symbol] = {}
            # brute force calculate all orderings with the new operator, this
            # could be more efficient by explicitly implementing a graph
            self.ordering[symbol][desc] = {}
            for o2 in self.ops[symbol]:
                self.ordering[symbol][desc][o2] = get_type_system().cmp(
                                    desc.arg_signature,
                                    types.freshen_type(o2.arg_signature))

                if self.ordering[symbol][desc][o2] is None:
                    self.ordering[symbol][o2][desc] = None
                else:
                    self.ordering[symbol][o2][desc] = -self.ordering[symbol][desc][o2]
            if self._term_re.match(symbol):
                if not symbol in self.exported and TypedExpr.has_local(symbol):
                    logger.warning(
                        f"Operator `{desc.name}/{desc.arg_signature}` shadows existing parsing local for `{symbol}`")
                TypedExpr.add_local(symbol, self.op_instantiator(symbol))
                self.exported.add(symbol)

        if not desc.arity in self.arities:
            self.arities[desc.arity] = dict()
        self.arities[desc.arity][desc] = desc

    def remove_operator(self, symbol, op):
        del self.ops[symbol][op]
        for o2 in self.ordering[symbol]:
            del self.ordering[symbol][o2][op]
        del self.ordering[symbol][op]
        if symbol in self.exported and symbol not in self.ops:
            TypedExpr.del_local(symbol)
            del self.exported[symbol]
        if op in self.arities[op.arity]:
            if not any(op in self.ops[symbol] for symbol in self.ops):
                # only delete from `arities` if no instances of op left
                del self.arities[op.arity][op]

    def get_operators(self, *types, symbol=None, arity=None, cls=None, exact=False):
        # this is currently basically a search function.
        # could add: filter on return type, way of doing the exact matching
        # algorithm in expr_factory, more general search on symbol names, ...
        if symbol is None:
            symbol = list(self.ops.keys())
        if not isinstance(symbol, collections.abc.Sequence) or isinstance(symbol, str):
            symbol = [symbol]
        # we use a dict for the initial pass to both preserve order, and avoid
        # duplicates for cases where an operator matches multiple symbols
        all_matches = {}
        for s in symbol:
            if s in self.ops:
                all_matches.update(self.ops[s])
        all_matches = list(all_matches.keys())

        if cls is not None:
            # almost certainly reduces to size 1 unless selecting multiple
            # symbols
            all_matches = [o for o in all_matches if o.cls == cls]

        if arity is not None:
            all_matches = [o for o in all_matches if o.arity == arity]

        if len(types): # get all; can't handle 0-ary operators if such a thing ever exists
            if exact:
                return [op for op in all_matches if op.check_types_viable(*types) == 0]
            else:
                return [op for op in all_matches if op.check_types_viable(*types) is not None]
        else:
            return all_matches

    def set_custom_transform(self, _cls, fun):
        # try to avoid using this...
        if fun is None:
            del self.custom_transforms[_cls]
        else:
            self.custom_transforms[_cls] = fun

    def apply_custom_transforms(self, _cls, e):
        if _cls in self.custom_transforms:
            return self.custom_transforms[_cls](e)
        else:
            return e

    def _find_closest(self, symbol, ops, min=True):
        # finds the least or greatest elements in `ops` in a topological sort.
        # the ordering could be memoized as well, since doing this each time
        # would cale badly with a lot of operators.
        # (n.b. I half-wrote and deleted a lot of graph code that is way, way
        # overengineered for the current state of things. But it may be worth
        # revisiting, since this should be doable in linear time by using
        # standard topological sorting algorithms.)
        if len(ops) <= 1:
            return ops
        result = []
        for o in ops:
            if min:
                antitarget = 1
            else:
                antitarget = -1
            # intentionally allows for None (e.g. using >= etc wouldn't work)
            if all([self.ordering[symbol][o][o2] != antitarget for o2 in ops]):
                result.append(o)
        return result

    def expr_factory_for(self, symbol):
        return lambda *args, **kwargs: self.expr_factory(symbol, *args, **kwargs)

    def op_instantiator(self, symbol):
        """Return a function that can be used to instantiate an operator in
        the metalanguage parser."""
        f = (lambda seq, **kwargs:
            call_from_te_seq(self.expr_factory_for(symbol), seq, **kwargs))
        f.__name__ = symbol
        f._meta_name_ = symbol
        return f

    def expr_factory(self, symbol, *args, **kwargs):
        """Given some operator/relation symbol with arguments, construct an
        appropriate TypedExpr subclass for that operator."""

        if not symbol in self.ops:
            raise parsing.ParseError(f"Unknown operator symbol `{symbol}`")

        matches = [o for o in self.ops[symbol].keys() if o.arity == len(args)]
        if not len(matches):
            raise parsing.ParseError(f"No {len(args)}-ary operator for `{symbol}`")

        matches = {o: o.check_viable(*args) for o in matches}

        # this code is very brute force, could be cleaner. The exact algorithm
        # here is subject to revision...

        # if there's an exact match, use the closest among those matches. The
        # reason for the sorting is cases like ({e},{X}) being ranked equal to
        # ({X},{X}) and (X,X), because it doesn't encode identity between the
        # coordinates; in a case like this we want to use ({X},{X}).
        result = self._find_closest(symbol, [o for o in matches if matches[o] == 0])
        if not result:
            # prefer specialized matches over generic matches, prioritizing the
            # one closest to the requested type.
            # * if there is an ambiguity in the specialized matches, look for
            #   an unambiguous generic match as a fallback. This is a bit ad
            #   hoc, since we don't do it for exact matches. (TODO: revisit)
            result = self._find_closest(symbol, [o for o in matches if matches[o] == -1], min=False)
            if len(result) != 1:
                # finally, try generic matches. If there are multiple generic
                # matches, prioritize the most specific one. E.g. ({e},{e})
                # given operators `(X,X)` and `({X},{X})` should match the
                # latter, because the former is even more generic.
                result = self._find_closest(symbol, [o for o in matches if matches[o] == 1])

        if not result:
            raise parsing.ParseError(
                f"No viable {len(args)}-ary operator for symbol `{symbol}` and arguments `{repr(args)}`")
        elif len(result) > 1:
            # this could be a lot more user-friendly, probably
            match_str = ", ".join(f"`{r.signature_str()}`" for r in result)
            raise parsing.ParseError(
                f"Ambiguous {len(args)}-ary operator symbol `{symbol}` for arguments `{repr(args)}`; compatible types: {match_str}")

        return self.apply_custom_transforms(result[0].cls, result[0].cls(*args, **kwargs))

    def add_binding_op(self, op):
        """Register an operator to be parsed."""
        if op.canonical_name is None:
            self.unparsed_binding_ops.add(op)
        else:
            # no binding operator overloading
            if op.canonical_name in self.binding_ops:
                logger.warning(
                    "Overriding existing binding operator `%s` in registry"
                    % op.canonical_name)
                self.remove_binding_op(op)
            self.binding_ops[op.canonical_name] = op
            if getattr(op, 'secondary_names', None):
                for alias in op.secondary_names:
                    self.canonicalize_binding_ops[alias] = op.canonical_name
        BindingOp.compile_ops_re()

    def remove_binding_op(self, op):
        """Remove an operator from the parsing registry."""
        for alias in self.binding_ops[op.canonical_name].secondary_names:
            del self.canonicalize_binding_ops[alias]
        if op.canonical_name is None:
            self.unparsed_binding_ops.remove(op)
        else:
            del self.binding_ops[op.canonical_name]
        BindingOp.compile_ops_re()

    def _repr_pretty_(self, p, cycle):
        if cycle:
            return "<Recursion in OperatorRegistry>"
        struc = self.ops.copy()
        for k in struc:
            struc[k] = list(self.ops[k].keys())
        p.pretty(struc)


def op_from_te(op_name, e, superclass=None, **kwargs):
    """Given some TypedExpr operator, produce a derived `SyncatOpExpr` subclass
    that uses that expression as its implementation."""
    if 'canonical_name' not in kwargs:
        kwargs['canonical_name'] = op_name

    op_arity = kwargs.get('arity', None)

    # a superclass will need to mimic SyncatOpExpr pretty closely to be usable
    # here...
    if superclass is None:
        superclass = SyncatOpExpr

    if not issubclass(superclass, SyncatOpExpr):
        raise ValueError(f"Operator wrapping requires a subclass of SyncatOpExpr (got: {repr(superclass)})")

    if not isinstance(e.type, types.FunType): # XX polymorphic e.type
        raise parsing.ParseError(
                f"Operator wrapping does not support 0-ary operators (tried to set `{op_name}` to non-function `{repr(e)}`)")

    if op_arity is None:
        if isinstance(e.type.left, types.TupleType):
            # pull the arity directly from a tuple type's arity
            # XX this allows for a 1-ary tuple
            op_arity = len(e.type.left)
        else: # FunType checked above
            # if the type and operator symbol support it, default to arity 2
            # when left unspecified
            if (isinstance(e.type.right, types.FunType) and (
                        op not in builtin_arities or 2 in builtin_arities[op])):
                op_arity = 2
            else:
                op_arity = 1

    # ternary operator support?
    if op_arity == 0 or op_arity > 2:
        raise parsing.ParseError(
                f"Operator wrapping does not support {op_arity}-ary operators (called on `operator {op_name}({op_arity}) = {repr(e)}`)")

    # store `e` with fresh type vars. XX it would be better if this were
    # handled by application, but it currently isn't (at least, not very well)
    e = e.copy().freshen_type_vars()

    if isinstance(e.type.left, types.TupleType):
        # XX this allows for a 1-ary tuple
        signature = e.type.left.signature
        rettype = e.type.right
    elif op_arity == 1:
        signature = (e.type.left,)
        rettype = e.type.right
    else:
        if not isinstance(e.type.right, types.FunType):
            raise parsing.ParseError(
                f"A 2-place operator requires an inner argument (called on `operator {op_name}({op_arity}) = {repr(e)}`)")
        # assumption: 2 place curried function
        signature = (e.type.left, e.type.right.left)
        rettype = e.type.right.right

    signature = types.TupleType(*signature)

    _secondary_names = kwargs.get('secondary_names', None)
    if _secondary_names is None:
        _secondary_names = set()

    # note: validation happens elsewhere
    is_py_op = not re.match(base_term_re, kwargs['canonical_name'])

    class WrappedOp(superclass):
        arity = op_arity
        # allow setting various class parameters via kwargs
        canonical_name = kwargs['canonical_name']
        secondary_names = _secondary_names
        op_name_uni = kwargs.get('op_name_uni', None)
        op_name_latex = kwargs.get('op_name_latex', None)
        operator_style = kwargs.get('operator_style', is_py_op)
        infix_style = kwargs.get('infix_style', is_py_op)
        commutative = kwargs.get('commutative', superclass.commutative)
        associative = kwargs.get('associative', superclass.associative)
        left_assoc = kwargs.get('left_assoc', superclass.left_assoc)
        pre_simplify = True # needs to be true for evaluation to work

        arg_signature = signature
        base_impl = e

        def __init__(self, *args, typ=None, **kwargs):
            if len(args) != self.arity:
                # call superclass without type checking so that the op
                # name is set correctly
                super().__init__(None, *args, typ=rettype, tcheck_args=False)
                # what exception type to use here?
                raise parsing.ParseError(
                    f"Operator `{self.op_name_uni}` needs {self.arity} operands but {len(args)} were given")

            # some fairly ugly type munging is currently needed here, because
            # just leaving it up to application can result in non-ideal inferred
            # types if both the operator and the arguments involve type
            # variables. (TODO)
            ttype = types.TupleType(*[a.type for a in args])
            ttype, _ = self.type_constraint(self.arg_signature, ttype)
            args = [self.type_constraint(args[i], ttype[i], constant=True) for i in range(len(signature))]
            if isinstance(self.base_impl[0].type, types.TupleType):
                impl_type = types.FunType(types.TupleType(args[0].type, args[1].type), self.base_impl[1].type)
            elif self.arity == 1:
                impl_type = types.FunType(args[0].type, self.base_impl.type[1])
            else:
                # assumption: 2-place curried function
                impl_type = types.FunType(args[0].type, types.FunType(args[1].type, self.base_impl[1][1].type))

            impl, _ = self.type_constraint(self.base_impl, impl_type)

            if isinstance(self.base_impl[0].type, types.TupleType):
                self._impl_composite = impl(Tuple(*args))
            elif self.arity == 1:
                self._impl_composite = impl(args[0])
            else:
                # assumption: 2-place curried function
                self._impl_composite = impl(args[0])(args[1])

            # Type inference should be done, validate the final output type
            self._impl_composite, typ = self.type_constraint(self._impl_composite, typ)
            super().__init__(None, *self._args_from_impl(), typ=typ, tcheck_args=False)

        def _args_from_impl(self):
            # pull arguments back out from a constructed self._impl_composite
            if isinstance(self._impl_composite[0].type, types.TupleType):
                return self._impl_composite[1].args
            elif self.arity == 1:
                return [self._impl_composite[1]]
            else:
                # assumption: 2-place curried function
                return [self._impl_composite[0][1], self._impl_composite[1]]

        def _compile(self):
            return self._impl_composite._compiled

        def simplify(self, **sopts):
            # derived will make a copy for most cases, but ensure that it
            # always does
            result = derived(self._impl_composite.copy(),
                self, desc=f"Evaluation of operator `{self.op_name_uni}`")

            if get_sopt('evaluate', sopts):
                # this is overly aggressive, but currently there's no better
                # way to sequence this
                # XX could wrap the guaranteed reduction steps with a better
                # derivation explanation?
                result = result.reduce_all() # may have side effects!

            return result

        @classmethod
        def random(cls, ctrl, typ=None, **kwargs):
            # XX input typ is discarded here
            args = [ctrl(typ=signature[i]) for i in range(cls.arity)]
            return cls(*args)

    # some metaprogramming to get better reprs for the class object.
    # These are not ideal, more-or-less the least worst options I have come
    # up with. The decorator below does better.
    WrappedOp.__name__ = op_name
    WrappedOp.__qualname__ = WrappedOp.__qualname__ + f".{op_name}"
    # leave __module__ as-is
    return WrappedOp


def op_class(*args, **kwargs):
    """Class decorator that can be used to generate a `SyncatOpExpr` from a
    TypedExpr providing an implementation, allowing for further programmatic
    overrides of the operator. Note that this uses multiple inheritence and
    that the decorated class *cannot* be an subclass of TypedExpr.

    The argument options are identical to those of `op_from_te`."""
    WrappedOpSuper = op_from_te(*args, **kwargs)

    def wrapper(cls):
        if issubclass(cls, TypedExpr):
            raise ValueError(f"@op_class cannot decorate a TypedExpr subclass (used on: `{repr(cls)}`)")
        # we can't set the superclass directly, so use multiple inheritence.
        # this leads to cute decorator code but it is reliant on the
        # superclasses not using multiple inheritence.
        # It is entirely possible this will be a bad idea in the long run...
        class WrappedOp(cls, WrappedOpSuper):
            pass
        WrappedOp.__name__ = cls.__name__
        WrappedOp.__qualname__ = cls.__qualname__
        WrappedOp.__module__ = cls.__module__
        return WrappedOp
    return wrapper


def is_op_symbol(op):
    global registry
    return op in registry.ops or op in builtin_arities


def op_expr_factory(op, *args, **kwargs):
    global registry
    if op == '[]':
        # not ideal to special case this, but this needs to be handled a bit
        # differently than other operators
        return TupleIndex(*args, **kwargs)
    return registry.expr_factory(op, *args, **kwargs)


def subassignment(assignment, _dict=None, **kwargs):
    from .meta import Assignment
    if assignment is None:
        r = {}
    elif (isinstance(assignment, collections.ChainMap)
                    or isinstance(assignment, Namespace)):
        r = assignment.new_child()
    else:
        # including Model
        r = collections.ChainMap({}, assignment)
    if _dict:
        r.update(_dict)
    r.update(kwargs)
    return r


############### Type unification-related code

class TermTypeMapping(object):
    """Holds a type mapping for a single term."""
    def __init__(self, term_name, principal, specializations=None, allow_poly=True):
        self.term_name = term_name
        self.principal = principal
        if allow_poly and principal.is_let_polymorphic() and specializations is None:
            specializations = set()
        self.specializations = specializations

    @property
    def let_polymorphic(self):
        return self.specializations is not None

    def get_type(self, specific=False):
        if specific and self.let_polymorphic and len(self.specializations) == 1:
            r, = self.specializations
            return r
        else:
            # multiple or 0 specializations, return the most general type
            # XX, in principle this should handle a sequence of more specific
            # types
            return self.principal

    def __repr__(self):
        # reprs do not show term names, because this is displayed in a
        # dict context
        if not self.let_polymorphic:
            return repr(self.principal)
        else:
            return f"{repr(self.principal)}[{', '.join(repr(s) for s in self.specializations)}]"

    def latex_str(self, **kwargs):
        if not self.let_polymorphic:
            return self.principal.latex_str()
        else:
            return f"{self.principal.latex_str()}[{', '.join(s.latex_str() for s in self.specializations)}]"

    def __str__(self):
        return f"{self.term_name}: {repr(self)}"

    def _clean_copy(self, principal):
        """Give a clean copy with principal type `principal`. No validation is
        done on `principal`. If the mapping is let-polymorphic, the primary
        polymorphic type will be preserved."""
        if self.let_polymorphic:
            # intended for use when principal is in self.specializations
            return TermTypeMapping(self.term_name, self.principal, {principal})
        else:
            return TermTypeMapping(self.term_name, principal, allow_poly=False)

    def copy(self):
        if self.let_polymorphic:
            return TermTypeMapping(self.term_name, self.principal, self.specializations.copy())
        else:
            return TermTypeMapping(self.term_name, self.principal, allow_poly=False)

    def sub_type_vars(self, mapping):
        # n.b. difference from a type object: this operates by side effect!
        if not mapping:
            return self
        self.principal = self.principal.sub_type_vars(mapping)
        if self.let_polymorphic:
            self.specializations = {t.sub_type_vars(mapping) for t in self.specializations}
        return self

    def bound_type_vars(self):
        r = self.principal.bound_type_vars()
        if self.let_polymorphic:
            for s in self.specializations:
                r = r | s.bound_type_vars()
        return r

    def merge(self, typ, env, allow_poly=True):
        allow_poly = allow_poly or self.let_polymorphic
        principal = env.try_unify(self.principal, typ, update_mapping=True)
        if principal is None:
            return None

        if allow_poly and (self.let_polymorphic or typ.is_let_polymorphic()):
            if self.let_polymorphic:
                # we have an existing polymorphic mapping, and will try to
                # update it, either changing the primary polymorphic type or
                # adding a specialization. The unify call above will find the
                # strongest of the two types if there is a difference.
                # there are basically four cases:
                # 1 principal == self.principal == typ: do nothing
                # 2 principal == self.principal, principal != typ: this means
                #   that typ should become the primary polymorphic type
                # 3 principal != self.principal, principal == typ: this means
                #   that typ should be added as a specialization
                # 4 principal != self.principal != typ: we would need a new
                #   primary polymorphic type and won't infer it, so failure.
                #   see note below.
                #
                # equality here is modulo alpha equivalence!
                # XX could call unify_details and check `trivial` for the
                # first case?

                # the unify call above will substitute type vars in the env, so
                # we need to match that
                ts = get_type_system()
                princ_equiv = ts.alpha_equiv(principal,
                    self.principal.sub_type_vars(env.type_mapping)) # XX is this needed?
                typ_equiv = ts.alpha_equiv(principal,
                    typ.sub_type_vars(env.type_mapping))
                if princ_equiv and typ_equiv:
                    # no new specialization
                    pass
                elif princ_equiv and not typ_equiv:
                    assert typ.is_let_polymorphic()
                    self.specializations.add(self.principal)
                    self.principal = typ
                elif not princ_equiv and typ_equiv:
                    self.specializations.add(typ)
                else: # not princ_equiv and not typ_equiv:
                    # unification succeeded, but the principal type is neither
                    # equivalent to self.principal or to typ. This means that we do
                    # not know what the primary let-polymorphic type actually is!
                    # merging should fail in this case.
                    #
                    # Example:
                    #     %te P_∀<<e,<X,Y>>,t>(x_Z) & P_∀<<Y,<X,e>>,t>(x_Z)
                    # Here, without further info, we cannot infer a single
                    # intended primary polymorphic type. E.g. is it
                    # `∀X`, `∀<X,Y>`, ∀`<<X,<Y,Z>>`, `∀<<Y,<X,Y>>`, ...?
                    # The last of these is for this case the strongest
                    # possible polymorphic type, but we don't try to infer
                    # this for the user. They'll need to specify it
                    # somehow. (XX is it possible in principle to do this
                    # inference in H-M?)
                    return None
            else: # not self.let_polymorphic
                assert typ.is_let_polymorphic()
                # we are lifting self to be let-polymorphic with `typ` as the new
                # primary polymorphic type
                self.specializations = {self.principal}
                self.principal = typ
        else: # not (self.let_polymorphic or typ.is_let_polymorphic())
            # no polymorphism, just replace `principal` if unification succeeds

            assert not allow_poly or not principal.is_let_polymorphic()
            self.principal = principal

        # final cleanup and return
        env.update_vars_in_terms() # XX side-effect-y
        return principal


class TypeEnv(object):
    def __init__(self, term_mapping=None, type_mapping=None):
        if term_mapping is None:
            term_mapping = dict()
        if type_mapping is None:
            type_mapping = dict()

        self.type_var_set = set()
        self.type_mapping = type_mapping
        self.term_mapping = term_mapping
        self.update_var_set()

    def _repr_html_(self):
        s = "<table>"
        s += ("<tr><td>Term mappings:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.dict_latex_repr(self.term_mapping))
        s += ("<tr><td>Type mappings:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.dict_latex_repr(self.type_mapping))
        s += ("<tr><td>Type variables:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.set_latex_repr(self.type_var_set))
        s += "</table>"
        return s

    def update_var_set(self):
        s = self.type_var_set
        s = s | types.vars_in_env(self.term_mapping)
        s = s | set(self.type_mapping.keys())
        for m in self.type_mapping:
            s  = s | self.type_mapping[m].bound_type_vars()
        self.type_var_set = s

    def used_vars(self):
        # requires up-to-date var set...
        return self.type_var_set - set(self.type_mapping.keys())

    def terms(self, sort=True):
        r = self.term_mapping.keys()
        if sort:
            # forces `r` to be a list
            # TODO: better sort orders?
            r = sorted(r)
        return r

    def term_type(self, t, specific=True):
        return self.term_mapping[t].get_type(specific=specific)

    def add_term_mapping(self, vname, typ, allow_poly=False):
        result = self.try_add_term_mapping(vname, typ, allow_poly=allow_poly)
        if result is None:
            # XX possibly error could be better set in term mapping code
            if self.term_mapping[vname].let_polymorphic:
                error = f"instances of term `{vname}` have mutually unresolvable polymorphism; can't infer primary polymorphic type"
                t2 = self.term_mapping[vname]
            else:
                error=f"instances of term `{vname}` have incompatible types"
                t2 = self.term_mapping[vname].principal
            raise TypeMismatch(typ, t2, error=error)
        return result

    def try_add_term_mapping(self, vname, typ, allow_poly=False):
        if vname in self.term_mapping:
            principal = self.term_mapping[vname].merge(typ, self, allow_poly=allow_poly)
            if principal is None:
                return None
        else:
            self.term_mapping[vname] = TermTypeMapping(vname, typ, allow_poly=allow_poly)
            principal = typ

        self.add_type_to_var_set(principal)
        return principal

    def remove_term(self, t):
        del self.term_mapping[t]

    def try_unify(self, t1, t2, update_mapping=False):
        ts = get_type_system()
        try:
            result = ts.unify_details(t1, t2, assignment=self.type_mapping)
        except types.OccursCheckFailure as e:
            # are there contexts where this should be raised?
            return None

        if result is None:
            return None
        else:
            if update_mapping:
                self.type_mapping = result.mapping
                self.update_var_set()
            return result.principal

    def add_type_to_var_set(self, typ):
        self.type_var_set = self.type_var_set | typ.bound_type_vars()

    def update_vars_in_terms(self):
        for k in self.terms():
            self.term_mapping[k].sub_type_vars(self.type_mapping)

    def try_add_type_mapping(self, type_var, typ, defer=False):
        if isinstance(typ, types.VariableType):
            if typ in self.type_var_set or type_var in self.type_var_set:
                principal = self.try_unify(type_var, typ, update_mapping=True)
            else:
                principal = type_var
                self.type_mapping[type_var] = typ
                self.type_var_set = self.type_var_set | {type_var, typ}                
        else:
            principal = self.try_unify(type_var, typ, update_mapping=True)
        if principal is not None and not defer:
            self.update_vars_in_terms()
        return principal

    def add_type_mapping(self, type_var, typ, defer=False):
        principal = self.try_add_type_mapping(type_var, typ, defer=defer)
        if principal is None:
            if type_var in self.type_mapping:
                raise TypeMismatch(self.type_mapping[type_var], typ,
                    error=f"Failed to unify type variable {type_var} across contexts")
            else:
                # XX better error message here
                raise TypeMismatch(type_var, typ,
                    error=f"Failed to unify type variable across contexts")
        return principal

    def _merge_term_mapping(self, v, m):
        self.add_term_mapping(v, m.principal, allow_poly=m.let_polymorphic)
        if m.specializations:
            for t in m.specializations:
                self.add_term_mapping(v, t, allow_poly=m.let_polymorphic)

    def merge(self, tenv):
        for v in tenv.type_mapping:
            self.add_type_mapping(v, tenv.type_mapping[v], defer=True)
        self.update_vars_in_terms()
        for v in tenv.term_mapping:
            self._merge_term_mapping(v, tenv.term_mapping[v])
        self.type_var_set |= tenv.type_var_set
        return self

    def intersect_merge(self, tenv):
        for v in tenv.type_mapping:
            if (v in self.type_var_set
                    or len(tenv.type_mapping[v].bound_type_vars()
                                                & self.type_var_set) > 0):
                self.add_type_mapping(v, tenv.type_mapping[v], defer=True)
        self.update_vars_in_terms()
        for v in tenv.term_mapping:
            self._merge_term_mapping(v, tenv.term_mapping[v])
        return self

    def copy(self):
        # ensure that copy is called on individual mappings
        m = {term: self.term_mapping[term].copy() for term in self.term_mapping}
        env = TypeEnv(m, self.type_mapping.copy())
        env.type_var_set = self.type_var_set.copy() # redundant with constructor?
        return env

    def __repr__(self):
        return ("[TypeEnv: Terms: "
            + repr(self.term_mapping)
            + ", Type mapping: "
            +  repr(self.type_mapping)
            + ", Type variables: "
            + repr(self.type_var_set)
            + "]")


def merge_tes(te1, te2, symmetric=True):
    """Produce a TypedExpr that is the result of 'merging' `te1` and `te2`.

    TypedExprs can be merged only if their types can match.  This has two types
    of behaviors:

    * Symmetric: if `te1` is a term and `te2` is not a term, return te2 coerced
        to the principal type; v.v for `te2` and `te1. Otherwise, if they are
        equal (using `==`, which checks structural/string identity) return the
        result at the principle type.
    * Non-symmetric: if `te1` is a term, return `te2` at the principal type. 
        Otherwise, return something (at the principal type) only if `te1` and
        `te2` are equal.
    The failure cases for both modes will raise a TypeMismatch.
    """
    # TODO: these error messages are somewhat cryptic
    principal = ts_unify_with(te1, te2,
                error="Failed to merge typed expressions (incompatible types)")
    te1_new = te1.try_adjust_type(principal)
    te2_new = te2.try_adjust_type(principal)
    if te1_new is None or te2_new is None:
        raise TypeMismatch(te1, te2,
                error="Failed to merge typed expressions (type adjustment failed)")
    if te1_new.term() and not te1_new.meta():
        if symmetric and te2_new.term() and not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                error="Failed to merge typed expressions; result is not equal")
        return te2_new
    elif symmetric and te2_new.term() and not te2_new.meta():
        return te1_new
    else:
        if not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                error="Failed to merge typed expressions; result is not equal")
        return te1_new


############### Core TypedExpr objects


global _parser_assignment
_parser_assignment = None


def call_from_te_seq(f, seq, **kwargs):
    # this function allows a function to be directly called from standard
    # argument syntax in the metalanguage parser. seq is either a single
    # argument, or a (t/T)uple giving a sequence of arguments. 

    seq = tenorm(seq)
    if (not is_te(seq) and not isinstance(seq, collections.abc.Sequence)
            or is_te(seq) and not isinstance(seq, Tuple)):
        # wrap any non-sequences as a 1-ary tuple
        seq = (seq,)
    else:
        seq = (tenorm(e) for e in seq)
    try:
        return f(*seq, **kwargs)
    except TypeError as e:
        raise parsing.ParseError(f"{f.__name__} instantiated with incorrect argument signature (`{str(e)}`)") from None


class TypedExpr(object):
    """Basic class for a typed n-ary logical expression in a formal language.
    This class should generally be constructed using the factory method, not the
    constructor.

    Three key fields:
      * type: an object that implements the type interface.
      * op: an object representing the operator in the expression.
      * args: _n_ args representing the arguments (if any) to the operator.

    The op field:
      * may be a string representing the operator symbol.  This case mostly
        covers special hard-coded logical/numeric operators. May be used in
        subclasses such as LFun.  NOTE: for hard-coded operators this is now
        deprecated, call the factory function.
      * May be itself a TypedExpr.  (For example, an LFun with the right type.)
        If so, there must be exactly one argument of the correct type.
      * May be a term name, treating this case as either a 0-ary operator or an
        unsaturated term. Note that right now, this _only_ occurs in
        subclasses. (TypedTerm)

    originally based on logic.Expr (from aima python), now long diverged.
    """

    canonical_name = None

    def __init__(self, op, *args, defer=False, typ=None):
        """
        Constructor for TypedExpr class. This class is an abstract class and
        should not be used directly. `TypedExpr.factory` may be used on this
        class to construct non-abstract `TypedExpr` instances. A subclass that
        does not call `__init__` should make sure that all necessary values
        here are still set.

        Parameters
        ----------
        op : str
            The operator's name. This is often cosmetic, but for terms, contains
            the term name.
        *args: list
            A sequence of arguments, to be assigned to self.args as a list.

        This is intended only for calls from subclass `__init__`.  It (at this
        stage) amounts to a convenience function that sets some common
        variables -- a subclass that does not call this should ensure that
        these are all set.  self.args must be a list (not a tuple).

        WARNING: this function may not set self.type, which _must_ be set.
        It does not perform any type-checking.

        `defer`: annotate with this if the TypedExpr does not conform to type
        constraints.  (Useful for derivational histories or error reports.)
        """
        self.type_guessed = False
        self.derivation = None
        self.defer = defer
        self.let = False
        if typ is not None:
            self.type = typ

        if (len(args) == 0):
            args = []

        self.op = op
        self.args = list(args)
        # tracks: during reduction, is arg i (currently) fully reduced?
        # False = no, None = tbd, True = yes
        # reset on copy without explicit handling
        self._reduced_cache = [None] * len(self.args)

    @classmethod
    def from_arg_seq(cls, seq, **kwargs):
        return call_from_te_seq(cls, seq, **kwargs)

    @classmethod
    def from_tuple(cls, seq, **kwargs):
        # backwards compatibility
        return cls.from_arg_seq(seq, **kwargs)

    @property
    def _type_cache(self):
        try:
            return self._type_adjust_cache
        except AttributeError:
            self._type_adjust_cache = dict()
            return self._type_adjust_cache

    def _type_cache_get(self, t):
        return self._type_cache.get(t, False)

    def _type_cache_set(self, t, result):
        self._type_cache[t] = result

    # this is a classmethod primarily for the error messaging
    @classmethod
    def type_constraint(cls, a, b, constant=False, error=None):
        """Given some elements `a` and `b`, attempt to reconcile types;
        return reconciled versions of `a` and optionally `b`.

        Parameters
        ----------
        a : `types.TypeConstructor` or `TypedExpr`
            The left element to attempt to reconcile
        b : `types.TypeConstructor` or `TypedExpr` or subclass of `types.TypeConstructor`
            The right element to attempt to reconcile
        constant : bool, default: False
            If `True`, treat the `b` element as a constant and don't return
            any modified versions. In this case, will fail if updating would
            adjust `b`. If `b` is a type constructor class, this must be True.
        error : str, optional
            An error message to use when raising TypeMismatch. If set to `None`,
            will construct one based on the class name. If set to False, don't
            error, but return None on failure.

        Returns
        -------
        tuple or `types.TypeConstructor` or `TypedExpr`
            If `constant` is False, return a tuple of (a,b) with any needed
            modifications. Otherwise, return a (potentially changed) version
            of `a`. May return `None` or `(None, None)`but only if `error` is
            `None`.
        """
        if cls.canonical_name:
            name = cls.canonical_name
        else:
            name = cls.__name__

        if isinstance(b, type) and issubclass(b, types.TypeConstructor):
            # XX: this case doesn't support error=False or setting error
            if is_te(a):
                a_typ = a.type
            else:
                a_typ = a
            if b == types.FunType:
                # special handling for functions, we can use tailored unify code
                # to do adjustment if needed.
                # XX could this be generalized? This essentially plugs type
                # variables in for arguments to the type constructor
                principal = get_type_system().unify_fun(a_typ, None, None)
                if principal is None:
                    raise TypeMismatch(a, b,
                        f"Failed to reconcile type constraint for `{name}`: {repr(a)} is a {b.__name__}")
                if principal != a_typ:
                    if constant:
                        raise TypeMismatch(a, b,
                            "Type constraint ({a} == constant {b.__name__}) would require adjusting constant to {principal}")
                    if is_te(a):
                        a = a.try_adjust_type(principal,
                            derivation_reason=f"Type constraint from {name}: {a_typ} == {b}")
                        if a is None:
                            raise TypeMismatch(
                                f"Failed to reconcile type constraint for `{name}`: {repr(a)} is a {b.__name__}")
                    else:
                        a = principal
                return a

            # otherwise, fail unconditionally on type class mismatch
            if not isinstance(a_typ, b):
                raise TypeMismatch(a, b,
                    f"Failed to reconcile type constraint for `{name}`: {repr(a)} is a {b.__name__}")
            # nothing else to be done
            return a

        if constant and isinstance(b, types.BasicType) and not is_te(a) and a in b.domain:
            # in principle this doesn't need the BasicType check, but it gets
            # expensive without, and I don't want to make a practice of
            # resolving domain elements via this call. This branch is primarily
            # for type_n and type_t...
            from .meta import MetaTerm
            return MetaTerm(a, typ=b, copying=True)

        if is_te(a):
            a_te = a
            a = a_te.type
            a_repr = f'`{repr(a_te)}`'
        else:
            a_te = None
            a_repr = f'type `{a}`'

        if is_te(b):
            b_te = b
            b = b_te.type
            b_repr = f'`{repr(b_te)}`'
        else:
            b_te = None
            b_repr = f'type `{b}`'

        def failed_constraint(a=a, b=b, a_te=None, b_te=None, error=error):
            if error is False:
                if constant:
                    return None
                else:
                    return None, None
            if a_te is not None:
                a = a_te
            if b_te is not None:
                b = b_te
            if is_te(a):
                a_repr = f'`{repr(a)}`'
            else:
                a_repr = f'type `{a}`'
            if is_te(b):
                b_repr = f'`{repr(b)}`'
            else:
                b_repr = f'type `{b}`'
            if error is None:
                error = f"Failed to reconcile type constraint for `{name}`: {a_repr} == {b_repr}"
            else:
                error = str.format(error, a_repr=a_repr, b_repr=b_repr, name=name)
            raise TypeMismatch(a, b, error=error)

        principal = ts_reconcile(a, b)
        if principal is None:
            return failed_constraint(a, b, a_te, b_te)
        if constant and b != principal:
            # is this unnecessarily strict?
            return failed_constraint(a, b,
                error=f"Type constraint for `{name}` ({a_repr} == constant {b_repr}) would require adjusting constant to {principal}")
        if principal is not None and a_te is not None:
            # XX maybe let caller set name for more information?
            a = a_te.try_adjust_type(principal,
                derivation_reason=f"Type constraint from {name}: {a} == {b}")
            if a is None:
                return failed_constraint(a_te, principal)
        else:
            a = principal
        if constant:
            return a
        if principal is not None and b_te is not None:
            b = b_te.try_adjust_type(principal,
                derivation_reason=f"Type constraint from {name}: {a} == {b}")
            if b is None:
                return failed_constraint(b_te, principal)
        else:
            b = principal
        return (a, b)

    def try_adjust_type_caching(self, new_type, derivation_reason=None,
                                            let_step=None):
        cached = self._type_cache_get(new_type)
        if cached is not False:
            return cached
        if let_step is not None:
            result = let_step.try_adjust_type(new_type,
                derivation_reason=derivation_reason)
            # TODO: freshen variables again here?
        else:
            result = self.try_adjust_type(new_type,
                derivation_reason=derivation_reason)
        self._type_cache_set(new_type, result)
        return result

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of `self` to be compatible with
        `new_type`.

        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it
          returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        env = self.get_type_env().copy()
        
        unify_target = env.try_unify(self.type, new_type, update_mapping=True)
        if unify_target is None:
            return None

        if self.type == unify_target:
            self._type_cache_set(self.type, self)
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            if self.term():
                new_term = self.copy()
                principal = env.try_add_term_mapping(new_term.op, new_type)
                if principal is None:
                    return None
                new_term.set_type_env(env)
                new_term.type = principal
                return derived(new_term, self, derivation_reason)
            else:
                # use the subclass' type adjustment function
                result = self.try_adjust_type_local(unify_target,
                                        derivation_reason, env)
                if result is not None:
                    result = result.under_type_assignment(env.type_mapping)
                    if result is not None:
                        result.set_type_env(env)
                if result is None:
                    # TODO: can this arise in current versions? Maybe convert
                    # to an exception? (This error is pretty old...)
                    logger.warning(
                        "In type adjustment, unify suggested a strengthened arg"
                        " type, but could not accommodate: %s -> %s"
                        % (self.type, unify_target))
                    return self
                else:
                    return derived(result, self, derivation_reason)

    def try_adjust_type_local(self, unified_type, derivation_reason, env):
        return self.copy_local(*self, typ=unified_type)

    @property
    def _type_env(self):
        try:
            return self._type_env_store
        except AttributeError:
            self._type_env_store = None
            return self._type_env_store

    def set_type_env(self, env):
        self._type_env_store = env

    def get_type_env(self, force_recalc=False):
        if force_recalc or self._type_env is None:
            self.set_type_env(self.calc_type_env(recalculate=force_recalc))
        return self._type_env

    def calc_type_env(self, recalculate=False):
        env = TypeEnv()
        for part in self:
            if isinstance(part, TypedExpr):
                env.merge(part.get_type_env(force_recalc=recalculate))
        return env

    def _compile(self):
        raise NotImplementedError

    def _compiled_repr(self):
        return f"<compiled {self.__class__.__name__} of type `{repr(self.type)}`>"

    @property
    def _compiled(self):
        if not getattr(self, '_compiled_cache', None):
            self._recompile()
        return self._compiled_cache

    def _recompile(self):
        self._compiled_cache = self._compile()
        if self._compiled_cache is not None:
            self._compiled_cache.__qualname__ = self._compiled_repr()
        return self._compiled_cache

    def _reset_compiled(self):
        self._compiled_cache = None

    def _unsafe_subst(self, i, s):
        self.args[i] = s
        return self

    def subst(self, i, s, assignment=None):
        s = TypedExpr.ensure_typed_expr(s)
        parts = list(self.args)
        old = parts[i]
        if not isinstance(old, TypedExpr):
            raise ValueError("Cannot perform substitution on non-TypedExpr %s"
                                                                    % (old))
        ts = get_type_system()
        # check: is the type of the substitution compatible with the type of
        # what it is replacing?
        # order matters: prioritize type variables from the substitution
        unified = ts_unify_with(s, old,
                    error=f"Substitution for element {i} of '{repr(self)}'")
        if unified != s.type:
            # compatible but unify suggested a new type for the substitution.  
            # Try adjusting the type of the expression.
            s_a = s.try_adjust_type(unified)
            # (can this fail if unify succeeded?)
            if s_a is None:
                raise TypeMismatch(s, old, error="Substitution for element %s of '%s'"
                                                            % (i, repr(self)))
            s = s_a
        parts[i] = s
        result = self.copy_local(*parts)
        return result

    def name_of(self, i):
        return f"subexpression {i}"

    @classmethod
    def parse(cls, s, assignment=None, locals=None):
        """Attempt to parse a string `s` into a TypedExpr
        `assignment`: a variable assignment to use when parsing.
        `locals`: a dict to use as the local variables when parsing.
        """
        # prevent reentrance from within an eval call
        if _parser_assignment is not None:
            # this can happen if a python string shows up in a metalanguage
            # expression. This solution is pretty hacky...
            raise parsing.ParseError("Invalid syntax", s=s)

        if assignment is None:
            assignment = dict()
        ts = get_type_system()
        (struc, i) = parsing.parse_paren_str(s, 0, ts)
        # Intercept any ParseError and update `s` to ensure we don't show strings
        # with replacements
        # TODO: this is generally a bit too wide. It'd be better to do something
        # like, show the biggest subexpression that has no replacements in which
        # the error occurred.
        with parsing.parse_error_wrap("Failed to parse expression", s=s, wrap_all=False):
            try:
                return tenorm(cls.try_parse_paren_struc_r(struc,
                                        assignment=assignment, locals=locals))
            except AttributeError as e:
                # convert AttributeError from TypedExprFacade.__getattr__ into a ParseError
                raise parsing.ParseError(str(e), s=s) from e

    _parsing_locals = dict()

    @classmethod
    def add_local(cls, l, value, raw=False):
        # ensure that variable capture is handled correctly
        ovalue = value
        if not raw and getattr(value, 'from_arg_seq', None):
            mname = getattr(value, 'canonical_name', value.__name__)
            value = lambda *args, **kwargs: ovalue.from_arg_seq(*args, **kwargs)
            value._meta_name_ = mname
        cls._parsing_locals[l] = value

    @classmethod
    def del_local(cls, l):
        if l == "TypedExpr" or l == "TypedTerm":
            raise Exception("Cannot delete parsing local '%s'" % l)
        del cls._parsing_locals[l]

    @classmethod
    def has_local(cls, l):
        return l in cls._parsing_locals

    @classmethod
    def try_parse_flattened(cls, s, assignment=None, locals=None):
        """Attempt to parse a flat, simplified string into a TypedExpr. Binding
        expressions should be already handled.
        
        assignment: a variable assignment to use when parsing.
        locals: a dict to use as the local variables when parsing.

        Do some regular expression magic to expand metalanguage terms into
        constructor/factory calls,  and then call eval.

        The gist of the magic (see expand_terms):
          * replace some special cases with less reasonable operator names.
            (This is originally based on AIMA logic.py)
          * find things that look like term names, and surround them with calls
            to the term factory function.

        Certain special case results are wrapped in TypedExprs, e.g. sets and
        tuples.
        """
        if locals is None:
            locals = {}

        if assignment is None:
            assignment = {}

        # handle an error case: if we try to parse this, it generates a
        # SyntaxError. But if None is returned, the caller can provide a
        # context-specific error.
        if not s.strip():
            return None

        # Replace the alternative spellings of operators with canonical
        # spellings
        to_eval = apply_op_aliases(s)
        lcopy = locals.copy()
        lcopy.update(cls._parsing_locals)
        pre_expansion = to_eval
        to_eval = TypedExpr.expand_terms(to_eval, assignment=assignment,
                                                            ignore=lcopy.keys())
        lcopy.update({'assignment': assignment, 'type_e': types.type_e})

        # cannot figure out a better way of doing this short of actually parsing
        # TODO: reimplement as a real parser, don't rely on `eval`
        global _parser_assignment
        _parser_assignment = assignment # not remotely thread-safe or reentrance-safe
        # Now eval the string.  (A security hole; do not use with an adversary.)
        try:
            result = eval(to_eval, dict(), lcopy)
        except SyntaxError as e:
            with parsing.parse_error_wrap("Binding expression parse error",
                                            s=pre_expansion):
                # try to induce some more informative error messages
                # if re.match(BindingOp.init_op_regex, pre_expansion):
                if BindingOp.init_op_match(pre_expansion):
                    BindingOp.try_parse_header([pre_expansion])
            # n.b. the msg here is probably just a placeholder, it should get
            # overridden.
            raise parsing.ParseError("Failed to parse expression", s=s, e=e)
            # other exceptions just get raised directly -- what comes up in
            # practice?
        finally:
            _parser_assignment = None

        result = tenorm(result)

        # XX is the container check needed here? code dup with factory
        if (c := from_python_container(result)) is not None:
            return c

        return validate_te(result)

    @classmethod
    def try_parse_binding_struc(cls, s, assignment=None, locals=None,
                                                            vprefix="ilnb"):
        """Try to parse `s` as a binding operator expression.  Will return a
        subclass of BindingOp, None, or raise a `parsing.ParseError`.

        the variable on the exception `met_preconditions` is used to attempt to
        figure out whether this was a plausible attempt at a binding operator
        expression, so as to get the error message right."""
        try:
            return tefnorm(
                BindingOp.try_parse_binding_struc_r(s,
                        assignment=assignment, locals=locals, vprefix=vprefix))
        except parsing.ParseError as e:
            if not e.met_preconditions:
                return None
            else:
                if not e.s:
                    e.s = parsing.flatten_paren_struc(s)
                    e.i = None # lost any context for this
                raise e

    @classmethod
    def try_parse_paren_struc_r(cls, struc, assignment=None, locals=None,
                                                            vprefix="ilnb"):
        """Recursively try to parse a semi-AST with parenthetical structures
        matched."""
        expr = cls.try_parse_binding_struc(struc, assignment=assignment,
                                                locals=locals, vprefix=vprefix)
        if expr is not None:
            return expr
        # struc is not primarily a binding expression
        s = ""
        h = dict()
        vnum = 1
        for sub in struc:
            if isinstance(sub, str):
                s += sub 
            else:
                sub_expr = cls.try_parse_paren_struc_r(sub,
                        assignment=assignment, locals=locals, vprefix=vprefix)
                if sub_expr is None:
                    # This might be unreachable: `()` parses as a 0-length
                    # tuple.
                    # probably could calculate `i`...
                    raise parsing.ParseError(
                        f"Empty subexpression {vnum}",
                        s=f"`{parsing.flatten_paren_struc(struc)}`")
                var = vprefix + str(vnum)
                s += f"({var})"
                vnum += 1
                h[var] = sub_expr
        return tefnorm(cls.try_parse_flattened(s, assignment=assignment, locals=h))


    @classmethod
    def expand_terms(cls, s, i=0, assignment=None, ignore=None):
        """Treat terms as macros for term_factory calls.  Attempt to find all
        term strings, and replace them with eval-able factory calls.

        This is an expanded version of the original regex approach; one reason
        to move away from that is that this will truely parse the types."""
        terms = find_term_locations(s, i)
        if ignore is None:
            ignore = set()
        offset = 0
        for t in terms:
            if t.start() + offset < i:
                # parsing has already consumed this candidate term, ignore.
                # (E.g. an "e" in a type signature.)
                continue
            (name, typ, end) = parse_term(s, t.start() + offset,
                                    return_obj=False, assignment=assignment)
            if name is None:
                logger.warning("Unparsed term '%s'" % t.group(0)) # TODO: more?
                continue
            elif name in ignore:
                continue
            # ugh this is sort of absurd
            if typ is None:
                replace = (f'__ptf("{name}", typ=None, assignment=assignment)')
            else:
                replace = (f'__ptf("{name}", typ="{repr(typ)}", assignment=assignment)')
            s = s[0:t.start() + offset] + replace + s[end:]
            i = t.start() + offset + len(replace)
            len_original = end - (t.start() + offset)
            offset += len(replace) - len_original
        return s

    @classmethod
    def term_factory(cls, s, typ=None, assignment=None, preparsed=False):
        """Attempt to construct a TypedTerm from argument s.

        If s is already a TypedTerm, return a copy of the term.
        If s is a string, try to parse the string as a term name.  (see
        try_parse_typed_term)
        Otherwise, fail.
        """
        ts = get_type_system()
        if isinstance(typ, str):
            typ = ts.type_parser(typ)

        aname = None
        # convert any assignments to MetaTerms to those MetaTerms, and then
        # set the corresponding assignment_name.
        # TODO: this is a bit ad hoc...
        if assignment is not None and s in assignment and assignment[s].meta():
            aname = s
            s = assignment[s]

        if is_te(s):
            if s.meta():
                # MetaTerms are immutable under all operations that call this, so
                # return without copying. (The only thing that may change across
                # instances with the same value is `derivation`.)
                if typ is not None:
                    s.check_type_domain(typ=typ)
                if aname is not None:
                    s = s.copy()
                    s.assignment_name = cls.term_factory(aname, s.type)
                return s
            elif s.term():
                # If `s` is already a term of some kind, make a copy. Note
                # that this will call a non-standard term class' copy.
                result = s.copy()
                if typ is not None:
                    result = result.try_adjust_type(typ)
                return result
            else:
                v = aname
                # fallthrough: construct a new term based on the term name.
                # Note: assignment could supply a non-term value here, but
                # the idea is that terms only get substituted on evaluation.
        elif types.is_type(s):
            # early return for this case, no further processing needed
            from .meta import MetaTerm
            return MetaTerm(s, typ=typ)
        else:
            if isinstance(s, str) and not preparsed:
                # in principle, if typ is supplied, could try parsing and
                # confirm the type?
                v, parsed_typ = try_parse_typed_term(s,
                                            assignment=assignment)
                if typ is not None and parsed_typ is not None:
                    principal = ts.unify(typ, parsed_typ)
                    if principal is None:
                        raise TypeMismatch(typ, parsed_typ,
                            f"Term `{s}` instantiated with inconsistent types")
                    typ = principal
                elif parsed_typ is not None:
                    typ = parsed_typ
                # else: both are None, leave typ as None
            else:
                # this does not validate term name formatting!
                v = s

        v = utils.num_or_str(v)
        if typ is not None:
            type_vars = typ.bound_type_vars() # ??

        if not isinstance(v, str) or v.startswith("_"):
            # casting behavior when parsing: pythonic conversions between
            # type t and n in both directions. For now this is *only* in
            # parsing, so (for example) is not visited by try_adjust_type.
            if v == 0 and not isinstance(v, bool) and typ == types.type_t:
                v = False
            elif types.is_numeric(v) and not isinstance(v, bool) and typ == types.type_t:
                v = True
            elif v == 0 and isinstance(v, bool) and typ == types.type_n:
                v = 0
            elif v == 1 and isinstance(v, bool) and typ == types.type_n:
                v = 1

            from .meta import MetaTerm
            r = MetaTerm(v, typ=typ)
            if aname is not None:
                r.assignment_name = cls.term_factory(aname, r.type)
            return r

        global _constants_use_custom
        if _constants_use_custom and not is_var_symbol(v):
            return CustomTerm(v, typ=typ, assignment=assignment)
        else:
            return TypedTerm(v, typ=typ, assignment=assignment)

    @classmethod
    def _construct_op(cls, op,  *args):
        # XX simplify to have only either this or op_expr_factory?
        def _op_factory(*args):
            return op_expr_factory(op, *args)
        return combine_with_type_envs(_op_factory, *args)

    @classmethod
    def _construct_appl(cls, *appl_args, assignment=None):
        def _appl_factory(f, *args):
            if len(args) > 1:
                arg = Tuple(*args)
            else:
                arg = args[0]
            if (not f.type.functional()) and f.type_guessed and _allow_coerced_types:
                # special case: see if the type of the operator is guessed and
                # coerce accordingly

                # prevent future coercion of the argument
                arg.type_not_guessed()
                coerced_f = f.try_coerce_new_argument(arg.type,
                                                        assignment=assignment)
                if coerced_f is not None:
                    logger.info(
                        "Coerced guessed type for '%s' into %s, "
                        "to match argument '%s'"
                        % (repr(f), coerced_f.type, repr(arg)))
                    f = coerced_f
                else:
                    logger.warning(
                        "Unable to coerce guessed type %s for '%s' "
                        "to match argument '%s' (type %s)"
                        % (f.type, repr(f), repr(arg), arg.type))
            return ApplicationExpr(f, arg, assignment=assignment)
        return combine_with_type_envs(_appl_factory, *appl_args)

    @classmethod
    def _composite_factory(cls, *args, assignment=None):
        # assumption: len(args) >= 1
        op = args[0]
        remainder = [cls.ensure_typed_expr(a) for a in args[1:]]
        if is_op_symbol(op) or op == '[]':
            return cls._construct_op(op, *remainder)

        # the only kind of operator-expression generated after this point is
        # an ApplicationExpr.
        op = cls.ensure_typed_expr(op)
        return cls._construct_appl(op, *remainder, assignment=assignment)

    @classmethod
    def factory(cls, *args, assignment=None, _globals=None, fullcopy=False):
        """Factory method for TypedExprs.  Will return a TypedExpr or subclass.

        Special cases:
          * single arg, is a TypedExpr: will return a copy of that arg.  (See
            ensure_typed_expr for alternate semantics.)
          * single arg, is a number/bool: will return a MetaTerm using that number.
          * single arg, is a valid `_` expression for a domain element: MetaTerm
          * single arg, is a variable/constant name: will return a TypedTerm
            using that name.  (Happens in parser magic.)
          * single arg, complex expression: will parse it using python syntax.
            (Happens in parser magic.)
          * multiple args: call the standard constructor.
        """
        ### NOTE: do not edit this function lightly...
        # XX remove this
        global _parser_assignment
        if assignment is None:
            if _parser_assignment is None:
                assignment = dict()
            else:
                assignment = _parser_assignment # not remotely thread-safe

        # `te` sets _globals by default, `factory` does not
        # n.b. for the case where _parser_assignment is set, `_globals` will
        # be already present in `assignment` via recursion on this function
        if _globals:
            assignment = collections.ChainMap(assignment, _globals)

        if len(args) == 0:
            return None #TODO something else?
        elif len(args) == 1:
            args = (tenorm(args[0]),)

            if isinstance(args[0], TypedExpr):
                # handing the factory function a single TypedExpr always returns
                # a copy of the object.
                result = args[0].copy()
                if fullcopy:
                    result.derivation = args[0].derivation
                return result

            # args[0] is either an unsaturated function, a term, or a string
            # that needs parsed.
            # in the first two cases, return a unary TypedExpr
            s = args[0]
            if s in types.type_t.domain: # generalize using get_element_type?
                return from_python(s, types.type_t)
            elif s in types.type_n.domain:
                return from_python(s, types.type_n)
            elif isinstance(s, str):
                return cls.parse(s, assignment)
            else:
                c = from_python_container(s)
                if c is not None:
                    return c
                # XX improve error messaging here?
                raise NotImplementedError # did you run a notebook with reload_lamb() out of order?
        else:
            # Argument length > 1.  
            # This code path is for constructing complex TypedExprs where
            # args[0] must be a function / operator. Will potentially recurse
            # via ensure_typed_expr on all arguments.
            return cls._composite_factory(*args, assignment=assignment)

    @classmethod
    def ensure_typed_expr(cls, s, typ=None, assignment=None):
        """Coerce s to a typed expression if necessary, otherwise, return s."""
        if isinstance(s, TypedExprFacade):
            s = s._e

        if isinstance(s, TypedExpr):
            if assignment is not None:
                result = s.under_assignment(assignment)
            else:
                result = s
        else:
            # XX consider removing this from this particular function
            try:
                result = te(s, assignment=assignment)
            except NotImplementedError:
                return validate_te(s)
        if typ is None:
            return result
        else:
            r_adjusted = result.try_adjust_type(typ)
            if r_adjusted is None:
                # make the reason a bit more coherent for people who don't
                # really know about type inference vs type checking
                reason = ((typ.is_polymorphic() or result.type.is_polymorphic())
                            and "type inference failure" or "type checking failure")
                raise TypeMismatch(result, typ, error=reason)
            else:
                return r_adjusted

    def try_coerce_new_argument(self, typ, remove_guessed=False,
                                                            assignment=None):
        return None

    def type_not_guessed(self):
        """Recursively set that the type of `self` is not a guess."""
        self.type_guessed = False
        if isinstance(self.op, TypedExpr):
            self.op.type_not_guessed()

    def copy(self):
        """Make a copy of the expression.  Will not produce a deep copy.

        Relies on a correctly implemented `copy_local`.
        """
        return self.copy_local(*self)

    def copy_core(self, other):
        # copy anything that is independent of self.args
        other.let = self.let
        return other

    def copy_local(self, *args, **kwargs):
        """
        Make a copy of the element preserving everything *except* the AST.

        The default implementation calls the constructor with `args`, so if this
        isn't appropriate, you must override."""
        return self.copy_core(type(self)(*args, **kwargs))

    def deep_copy(self):
        accum = list()
        for p in self:
            if isinstance(p, TypedExpr):
                accum.append(p.deep_copy())
            else:
                accum.append(p)
        return self.copy_local(*accum, copying=True)

    def regularize_type_env(self, assignment=None, constants=False,
                                                                target=None):
        if assignment is None:
            assignment = dict()
        env = self.get_type_env()
        # note: this will cut off any derivations without handling from the
        # caller. But we typically don't want the immediately prior version in
        # the record, since the types could be quite messy.
        return self.under_type_assignment(env.type_mapping,
                                                        merge_intersect=False)

    def compact_type_vars(self, unsafe=None, store_mapping=False):
        return let_compact_type_vars(self, unsafe=unsafe,
                                            store_mapping=store_mapping)


    def freshen_type_vars(self, target=None,
                                used_vars_only=False,
                                store_mapping=False,
                                force=False):
        if not self.let and not force:
            return self
        history_env = self.get_type_env()
        if len(history_env.type_var_set) == 0:
            return self
        c = self.copy()
        # note: the following is already triggered by copy.  If this behavior
        # changes, this needs updating.
        env = c.get_type_env()
        if used_vars_only:
            tenv = env.type_var_set - set(env.type_mapping.keys())
        else:
            tenv = env.type_var_set
        if len(tenv) == 0:
            return self
        fresh_map = types.freshen_type_set(tenv)
        # XX result vs c??
        result = self.under_type_injection(fresh_map)
        result._type_env_history = history_env
        if not store_mapping:
            result.get_type_env(force_recalc=True)
        result.let = False
        return result

    def let_type(self, typ):
        result = self.try_adjust_type(typ)
        if result is None:
            return None
        if result.let:
            result = let_wrapper(result)
        return result

    def has_type_vars(self):
        return len(self.get_type_env().type_var_set) > 0

    def _unsafe_under_type_injection(self, mapping):
        if len(mapping) == 0:
            return self
        for i in range(len(self)):
            self._unsafe_subst(i, self[i].under_type_injection(mapping))
        self.type = self.type.sub_type_vars(mapping)
        return self

    def under_type_injection(self, mapping):
        accum = list()
        for p in self:
            accum.append(p.under_type_injection(mapping))
        r = self.copy_local(*accum, copying=True)
        r.type = r.type.sub_type_vars(mapping)
        if r.term():
            r.get_type_env(force_recalc=True)
        return r

    def under_type_assignment(self, mapping, reset=False, merge_intersect=True):
        # TODO: For somewhat irritating reasons, this is currently a _lot_
        # slower if reset=True

        if len(mapping) == 0:
            return self
        dirty = False
        parts = list()
        for part in self:
            new_part = part.under_type_assignment(mapping, reset=reset)
            if new_part is not part:
                dirty = True
            else:
                if reset:
                    new_part = new_part.copy()
                    new_part.get_type_env(force_recalc=True)
            parts.append(new_part)
        # this may or may not be recalculated by copy_local.  The main case
        # where it isn't is terms.
        copy_type = self.type.sub_type_vars(mapping)
        # Note: we still need to reset the subordinate type environments even
        # in this case.
        if copy_type == self.type and not dirty:
            return self
        result = self.copy_local(*parts)
        if result.term():
            result.type = copy_type
        if reset:
            result.get_type_env(force_recalc=True)

        # order in the following is important. If the two envs have competing
        # mappings, e.g. X1:?1 and ?1:X1, then we want to prioritize the
        # mapping from the `mapping` argument to this function.
        if merge_intersect:
            result.set_type_env(TypeEnv(type_mapping=mapping).intersect_merge(
                                                result.get_type_env()))
        else:
            result.set_type_env(TypeEnv(type_mapping=mapping).merge(
                                                result.get_type_env()))

        # need to set a derivation step for this in the calling function.
        set_derivation(result, self.derivation)
        return result

    def under_assignment(self, assignment, track_all_names=False, compact=False):
        """Use `assignment` to replace any appropriate variables in `self`."""
        # do this first so that any errors show up before the recursive step
        # this does not set a derivation!
        if assignment is None:
            a2 = dict()
        else:
            # XX is this really necessary?
            a2 = {key: self.ensure_typed_expr(assignment[key])
                                                        for key in assignment}
        # if an expression consisting of just a term name is replaced, we may
        # lose the current let state
        let = self.let
        r = term_replace_unify(self, a2, track_all_names=track_all_names)
        # XX I'm not sure this should be conditional..
        if (let or r.let) and compact:
            r = let_wrapper(r)
        # XX name this differently depending on where the assignment comes from?
        return derived(r, self, "Assignment substitution")

    def free_terms(self, var_only=False):
        """Find the set of variables that are free in the typed expression.
        """
        v = set(self.get_type_env().terms())
        if var_only:
            v = {var for var in v if symbol_is_var_symbol(var)}
        return v

    def free_variables(self):
        return self.free_terms(var_only=True)

    def bound_variables(self):
        """Find the set of variables that are bound (somewhere) in a typed
        expression.

        Note that this may be overlapping with the set of free variables.
        """
        result = set()
        for a in self.args:
            result.update(a.bound_variables())
        return result

    def find_safe_variable(self, starting="x", avoid_bound=True, blockset=None):
        """Find an a safe alpha variant of the starting point (by default: 'x'),
        that is not used in the expression."""
        if blockset is None:
            blockset = set()
        blockset = blockset | self.free_variables()
        if avoid_bound:
            blockset = blockset | self.bound_variables()
        varname = alpha_variant(starting, blockset)
        return varname

    def term(self):
        return False

    def meta(self):
        return False

    def term_parent(self):
        return all(a.term() for a in self)

    def functional(self):
        # XX a really general implementation of this might want to unify with
        # <?,?> or <X,Y> where X,Y are `fresh_for` self.type. However, doing
        # so is quite inefficient in a way that can occasionally add up...
        return self.type.functional()

    def atomic(self):
        return len(self.args) == 0

    @classmethod
    def _default_simplify_args(cls, *args, origin=None, **sopts):
        # wraps a point `simplify` implementation to be usable with the
        # multisimplify code
        e = cls(*args)
        if origin is None:
            origin = e
        else:
            e = derived(e, origin, allow_trivial=False)
        result = e.simplify(**sopts)
        if e is result:
            return None
        return result

    def simplify(self, **sopts):
        """Simplify an expression "locally", i.e. non-recursively. The exact
        behavior is heavily dependent on the kind of expression in question.

        See also
        --------
        simplify_all: the api to trigger full recursive simplification

        """
        # simplification behavior can also be defined via a classmethod that
        # takes ordered arguments. If a subclass defines this method, by
        # default use that. This lets subclasses write either an overridden
        # simplify, or the classmethod.
        if getattr(self, 'simplify_args', None):
            if get_sopt('collect', sopts) and collectable(self):
                early_check = getattr(self, 'simplify_early_check', None)
                # non-recursive multisimplify call
                return multisimplify(self,
                    simplify_fun=self.simplify_args,
                    early_check=early_check,
                    ctrl=None, # XX is this needed?
                    **sopts)
            else:
                # just call `simplify_args` with self.args; this is the
                # `simplify_point` strategy
                r = self.simplify_args(*self.args, origin=self, **sopts)
                if r is not None:
                    return r
        # default behavior: no change
        return self

    def eliminate(self, **sopts):
        return self

    def _multisimplify_wrapper(self, ctrl=None, **sopts):
        if getattr(self, 'simplify_args', None):
            simplify_args = self.simplify_args
        elif associative(self):
            simplify_args = self._default_simplify_args
        else:
            simplify_args = None # no local simplify call!
        early_check = getattr(self, 'simplify_early_check', None)
        return multisimplify(self,
                simplify_fun=simplify_args,
                early_check=early_check,
                ctrl=ctrl,
                **sopts)

    def simplify_collected(self, pre=False, **sopts):
        """General purpose recursive simplification strategy for expressions
        that may be collectable into n-ary lists via `collect`. (E.g. `&`, `|`
        expressions.)

        See also
        --------
        multisimplify: the implementation of the collect+simplify algorithm.
        """
        e = self
        if pre:
            # non-recursive call; it's still a bit painful to do this twice...
            e = e._multisimplify_wrapper(**sopts)
            # note: `e` can be a different class than `self` at this point

        return e._multisimplify_wrapper(ctrl=simplify_all, **sopts)

    def simplify_point(self, pre=False, **sopts):
        """General purpose recursive simplification strategy; this assumes
        nothing about the class behavior, and does all simplification via local
        `simplify` only. It does not apply any multi-expression normalizations,
        e.g. alphanorm.
        """
        result = self
        if pre:
            result = result.simplify(**sopts)
            # not very elegant -- if presimplification has generated a Partial,
            # drop into the Partial implementation of simplify_point instead.
            if isinstance(result, Partial):
                return result.simplify_point(sopts)
        for i in range(len(result.args)):
            # simple: go left to right, no repeats.
            new_arg_i = result.args[i]._simplify_all_r(**sopts)
            if new_arg_i is not result.args[i]:
                result = derived(result.subst(i, new_arg_i), result,
                    desc=f"Recursive simplification of {result.name_of(i)}",
                    subexpression=new_arg_i)
        return result.simplify(**sopts)

    def simplify_all(self, pre=False, **sopts):
        """
        Simplify an expression recursively. The exact behavior is heavily
        dependent on the details of the expression in question.
        Simplification is heuristic: it generally attempts to shorten
        expressions where possible and where it knows how, but it is neither a
        substitute for a human theorist or a true theorem prover! The
        transformations it applies are more analogous to typical preprocessing
        steps for a theorem prover.

        If an expression consists only of MetaTerms, it will generally be fully
        interpreted.

        Examples
        --------
        >>> te("False & True").simplify_all()
        False_t

        >>> te("True & p_t").simplify_all()
        p_t

        >>> te("p_t & (P(x) & (p_t | True))").simplify_all()
        (p_t ∧ P_<e,t>(x_e))

        >>> te("p_t & (P(x) & (p_t | True))").simplify_all().derivation
        1. (p_t & (P_<e,t>(x_e) & (p_t | True_t)))
        2. [p_t, P_<e,t>(x_e), (p_t | True_t)]    (alphabetic normalization)
        3. [p_t, P_<e,t>(x_e), True_t]    ([[disjunction]])
        4. [p_t, P_<e,t>(x_e)]    ([conjunction])
        5. (p_t & P_<e,t>(x_e))    (join on ∧)
        """
        # nb the examples in the docstring are tested in ipython, not the
        # regular interpreter...

        result = self
        initial_let = result.let
        # don't apply `reduce` or `calc_partiality` recursively, since they are
        # already recursive. Any subcall that restarts simplify_all will
        # trigger them, though.
        if get_sopt('reduce', sopts):
            result = result.reduce_all()

        if get_sopt('calc_partiality', sopts):
            # similarly, don't apply calculate_partiality recursively. Note that
            # calculate_partiality may itself call simplify_all.
            sopts['calc_partiality'] = False

        result = result._simplify_all_r(pre=pre, **sopts)
        if get_sopt('reduce', sopts) and result.subreducible() and result is not self:
            # sigh, simplification has generated some expressions that now need
            # reduction. We need to start everything over again.
            # XX the `self` check is an inelegant way to avoid infinite loops
            # if there are bugs in reducible.
            # XX what about `evaluate`?
            return result.simplify_all(pre=pre, **sopts)
        if result.let or initial_let:
            result = let_wrapper(result)
        return result

    def _simplify_all_r(self, pre=False, **sopts):
        result = self
        # do this before the normal simplify pass, since it almost guarantees
        # something that will feed the rest of simplification
        while get_sopt('eliminate_quantifiers', sopts) and isinstance(result, BindingOp):
            # currently, only quantifiers and ConditionSet actually implement
            # `eliminate`...
            # this is subject to combinatorial blowup with the size of the domain
            r2 = result.eliminate(**sopts)
            if r2 is result:
                break
            result = r2

        collect = get_sopt('collect', sopts) and collectable(result)
        pre = pre or getattr(result.__class__, 'pre_simplify', False)
        if collect and associative(result):
            return result.simplify_collected(pre=pre, **sopts)
        else:
            if (collect and get_sopt('alphanorm', sopts)
                    and left_commutative(result) or right_commutative(result)):
                # collectable, not associative, but still at least partially
                # commutative (e.g. BindingOp). Apply alphanorm here. Note that
                # this strategy is inefficient in that it will do this on every
                # recursive step. (TODO)
                result = alphanorm(result)
            return result.simplify_point(pre=pre, **sopts)

    def reducible(self):
        return False

    def will_reduce(self, arg):
        return False

    def reduce(self):
        return self

    def _is_reduced_caching(self):
        if len(self) == 0:
            return True
        if self.reducible():
            return False
        seen_true = False
        for i in self._reduction_order():
            if self._reduced_cache[i]:
                seen_true = True
            elif self._reduced_cache[i] == False:
                return False
        return seen_true or None

    def _do_reduce(self, strict_charfuns=True):
        from .meta import OutOfDomain
        try:
            return self.reduce() # this will add a derivation
        except OutOfDomain as e:
            # n.b. this relies on some assumptions about where OutOfDomain
            # can be thrown from...
            if self.type == types.type_t and not strict_charfuns:
                return from_python(False)
            else:
                raise e

    def subreduce(self, path, reason=True, force_full=True, use_cache=True,
                        strict_charfuns=True):
        if not path:
            return self._do_reduce(strict_charfuns=strict_charfuns)
        i = path[0]
        if not use_cache or not self._reduced_cache[i]:
            if force_full:
                # continue recursing along the exact `path`
                new_arg_i = self[i].subreduce(path[1:],
                                    force_full=force_full,
                                    reason=True,
                                    use_cache=use_cache)
            else:
                # there are unreduced elements at this point along the path.
                # Look for them via pair recursion with reduce_all. This is
                # useful (and the default for reduce_all calls) because it
                # produces better derivations.
                new_arg_i = self[i].reduce_all(use_cache=use_cache,
                                                group_recursion=True)
            if new_arg_i is not self[i]:
                args = list(self.args)
                args[i] = new_arg_i
                result = self.copy_local(*args)
                if reason:
                    if force_full:
                        if reason and reason is True:
                            reason = f"reduction of path {repr(path)}"
                        # bookkeeping is a bit annoying for this case
                        # (because of sequences like (0,0,0) and then (0,0)),
                        # so don't track the recursive detail at all. If this
                        # were ever used by the automatic algorithm, this
                        # should be fixed.
                        subexpression = None
                    else:
                        reason = f"recursive reduction of {self.name_of(i)}"
                        subexpression = new_arg_i
                    result = derived(result, self,
                            desc=reason,
                            subexpression=subexpression)
                else:
                    # prevent reason=False from wiping out an existing
                    # derivation. (XX does this have any weird effects?)
                    set_derivation(result, self.derivation)
                result._reduced_cache = self._reduced_cache.copy()
                # sync any changes to i's _reduced_cache:
                result._reduced_cache[i] = result[i]._is_reduced_caching()
                return result
        return self

    def _reduction_order(self):
        return range(len(self))

    def subreducible(self, use_cache=True, group_recursion=True):
        # depth first search for a reducible element. This memoizes. If
        # `use_cache` is False, it does not check the cache when recursing
        # (but still updates the cache).
        if self.reducible():
            return ()
        for i in self._reduction_order():
            if use_cache and self._reduced_cache[i] is not None:
                if self._reduced_cache[i]:
                    continue
                elif group_recursion:
                    # note: this case returns an incomplete path
                    return (i,)
                # else: intentional fallthrough. Find the exact reducible
                # element in the cached path.
            path = self[i].subreducible(use_cache=use_cache,
                                        group_recursion=group_recursion)
            if path is not None:
                self._reduced_cache[i] = False
                return (i,) + path
            else:
                self._reduced_cache[i] = True
        return None

    def reduce_all(self, group_recursion=True, use_cache=True):
        """Maximally reduce function-argument combinations in `self`."""

        # uncomment this to see how bad this function is...
        # dbg_print(f"reduce_all on '{repr(self)}'")
        result = self

        # `subreducible` calls will build a chart for subexpressions they
        # visit, and `subreduce` will update that chart.
        # TODO: right now the chart is stored on TypedExpr objects. It might
        # be better to simply build the chart independently during recursion
        # here?
        path = result.subreducible(group_recursion=group_recursion,
                                    use_cache=use_cache)
        while path is not None:
            # `force_full` here can lead to less efficient derivation
            # sequences, but more comprehensible derivations.
            result = result.subreduce(path,
                reason=True,
                force_full=not group_recursion,
                use_cache=use_cache)
            path = result.subreducible(group_recursion=group_recursion,
                                        use_cache=use_cache)

        return result

    def calculate_partiality(self, vars=None, **sopts):
        from .boolean import BinaryAndExpr, true_term
        condition = []
        result = self
        for i in range(len(self)):
            part_i = result[i].calculate_partiality(vars=vars, **sopts)
            while isinstance(part_i, Partial):
                condition.append(part_i.condition)
                part_i = derived(part_i.body.copy(),
                    part_i,
                    "Partiality (remove conditions from body)")

            if part_i is not result[i]:
                result = derived(result.subst(i, part_i),
                    result,
                    f"Partiality calculation (recursion on {result.name_of(i)})",
                    subexpression=part_i)
        if condition:
            condition = BinaryAndExpr.join(condition, empty=true_term)
            intermediate = derived(Partial(result, condition), result,
                                            "Partiality (merge conditions from body)",
                                            subexpression=condition)
            # calling Partial.calculate_partiality() may further simplify
            return intermediate.calculate_partiality(vars=vars, **sopts)
        else:
            return result


    def __call__(self, *args):
        """Attempt to construct a saturated version of self.  This constructs a
        composite TypedExpr, with the function (`self`) as the operator and the
        argument(s) as the arguments.  Type checking happens immediately."""
        
        return TypedExpr.factory(self, *args)


    def __repr__(self):
        """Return a string representation of the TypedExpr.

        This is guaranteed (barring bugs) to produce a parsable string that
        builds the same object.
        """
        # default repr code: should be able to handle most cases without too
        # much weirdness. Handles term-like elements (len 0), unary operators,
        # n-ary operators in either prefix or infix form.
        name = getattr(self, 'canonical_name')
        if name is None:
            name = self.op
        if len(self.args) == 1:
            if getattr(self, 'operator_style', False):
                return f"{name}{repr(self.args[0])}"
            else:
                # using utils.parens here relies on infix operator code
                # guaranteeing parentheses. If that code ever returned
                # anything like `(1+2)+(3+4)`, this wouldn't be safe.
                return f"{name}{utils.parens(repr(self.args[0]))}"
        else:
            if getattr(self, 'infix_style', False):
                op_text = f" {name} "
                return "(%s)" % (op_text.join([repr(a) for a in self.args]))
            else:
                if len(self.args) == 0 and getattr(self, 'term_style', False):
                    # note that term subclasses don't use this branch, they
                    # override
                    return f"{name}"
                else:
                    return f"{name}({', '.join([repr(a) for a in self.args])})"

    # XX default _repr_pretty_?

    def latex_str(self, suppress_parens=False, **kwargs):
        """Return a representation of the TypedExpr suitable for Jupyter
        Notebook display.

        The output should be pure LaTeX (i.e., no HTML)."""

        # default latex output, should be able to handle most basic cases.
        # SyncatOpExpr has more sophisticated code. (XX: can these be unified?)

        # past this point in the list of cases should only get hard-coded
        # operators
        if len(self.args) == 1: # Prefix operator
            if getattr(self, 'operator_style', False):
                return ensuremath(
                    f"{self.op}{self.args[0].latex_str(**kwargs)}")
            else:
                return ensuremath(
                    f"{self.op}({self.args[0].latex_str(suppress_parens=True, **kwargs)})")
        else:
            if getattr(self, 'infix_style', False):
                base = f" {self.op} ".join([a.latex_str(**kwargs) for a in self.args])
                if not suppress_parens:
                    base = f"({base})"
                return ensuremath(base)
            else:
                if len(self.args) == 0 and getattr(self, 'term_style', False):
                    # note that term subclasses don't use this branch, they
                    # override
                    return ensuremath(f"{self.op}")
                else:
                    arg_str = ", ".join(a.latex_str(suppress_parens=True, **kwargs) for a in self.args)
                    return ensuremath(f"{self.op} ({arg_str})")

    def _repr_latex_(self):
        return self.latex_str(suppress_parens=True)

    def __str__(self):
        if self.term():
            return self.__repr__()
        else:
            # should this just return repr unconditionally?
            return f"{self.__repr__()}, type {self.type}"

    def _eq_elem(self):
        return tuple(self.args)

    def __eq__(self, other):
        """x and y are equal iff their ops and args are equal.

        Note that this is a _syntactic_ notion of equality, not a _semantic_
        notion -- for example, two expressions would fail this notion of
        equality if one reduces to the other but that reduction has not been
        done.  Alphabetic variants will also not come out as equal."""

        # need to explicitly check this in case recursion accidentally descends into a string Op
        # TODO revisit
        if isinstance(other, TypedExpr):
            return (other is self
                or (self.op == other.op
                    and self._eq_elem() == other._eq_elem()
                    and self.type == other.type))
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.op) ^ hash(self._eq_elem()) ^ hash(self.type)

    def __getitem__(self, i):
        """If `i` is a number, returns a part of `self` by index.  
        index 0 always gives the operator.
        index >=1 gives whatever arguments there are.  Note that this is
        shifted from the indexing of `self.args`.

        If `i` is a TypedExpr, try to construct an expression representing
        indexing."""
        if isinstance(i, TypedExpr) or isinstance(i, TypedExprFacade):
            return self.factory('[]', self, i)
        else:
            return self.args[i]

    def __len__(self):
        """Return the number of parts of `self`, including the operator."""
        return len(self.args)

    # See https://docs.python.org/3/reference/datamodel.html
    # Not implemented: not, abs, pos, concat, contains, *item, *slice,
    def __and__(self, other):    return self.factory('&',  self, other)
    def __invert__(self):        return self.factory('~',  self)
    def __lshift__(self, other): return self.factory('<<', self, other)
    def __rshift__(self, other): return self.factory('>>', self, other)
    def __or__(self, other):     return self.factory('|',  self, other)
    def __xor__(self, other):    return self.factory('^',  self, other)
    def equivalent_to(self, other): return self.factory('<=>',  self, other)
    def __mod__(self, other):    return self.factory('%',  self, other)

    def __lt__(self, other):     return self.factory('<',  self, other)
    def __le__(self, other):     return self.factory('<=', self, other)
    def __add__(self, other):    return self.factory('+',  self, other)
    def __sub__(self, other):    return self.factory('-',  self, other)
    def __div__(self, other):    return self.factory('/',  self, other)
    def __truediv__(self, other):return self.factory('/',  self, other)
    def __floordiv__(self, other):return self.factory('//',  self, other)
    def __mul__(self, other):    return self.factory('*',  self, other)
    def __neg__(self):           return self.factory('-',  self)
    def __pos__(self):           return self.factory('+',  self)
    def __pow__(self, other):    return self.factory('**', self, other)
    def __matmul__(self, other): return self.factory('@', self, other)

    # add reverse versions of several of the above so that things like
    # `2 + te("2")` work. Python has a weird special case where if you do
    # A + B where `B` is a subclass of `A`, it'll call the reverse version
    # on `B` if possible. To avoid this for the case of `Term`/`MetaTerm`,
    # explicitly prevent the reverse versions from working if `other` is a
    # TypedExpr.
    def __radd__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('+', other, self)

    def __rsub__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('-', other, self)

    def __rtruediv__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('/', other, self)

    def __rfloordiv__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('//', other, self)

    def __rmul__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('*', other, self)

    def __rpow__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('**', other, self)

    def __rmatmul__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('@', other, self)

    def __rmod__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('<=>', other, self)

    def __rand__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('&', other, self)

    def __ror__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('|', other, self)

    def __rxor__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('^', other, self)

    def __rrshift__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('>>', other, self)

    def __rlshift__(self, other):
        if is_te(other):
            return NotImplemented
        return self.factory('<<', other, self)

    # because __ge__ is used both as a reverse for __le__, and when >= is used
    # directly, we can't use the above trick to ensure the constructed order
    # is the same as what the user typed. I haven't come up with a solution
    # short of making `MetaTerm` not a subclass of `Term`.
    def __ge__(self, other):
        return self.factory('>=', self, other)

    def __gt__(self, other):
        return self.factory('>',  self, other)

    def __bool__(self):
        # otherwise, python tries to use the fact that these objects implement a
        # container interface to convert to bool, which can lead to weird
        # results. This is overridden in exactly one place, `MetaTerm`.
        return True

    @property
    def M(self):
        return TypedExprFacade(self)


def __ptf(s, typ=None, assignment=None):
    return TypedExpr.term_factory(s, typ=typ, assignment=assignment).M


TypedExpr.add_local('__ptf', __ptf, raw=True)


class TypedExprFacade(object):
    def __init__(self, e):
        if isinstance(e, TypedExprFacade):
            e = e._e # no recursion
        self._e = e

    @property
    def M(self):
        return self

    def __getattr__(self, name):
        global registry
        matches = registry.get_operators(arity=1, symbol=name)
        if not matches:
            # this has to be AttributeError or it breaks the api
            # for parsing, this exception is later converted to ParseError
            raise AttributeError(
                f"Unknown postfix unary operator `{name}` for expression type `{self._e.type}`")
        return TypedExpr.factory(name, self._e).M

    # Not implemented: not, abs, pos, concat, contains, *item, *slice, len
    def __and__(self, other):    return self._e.__and__(other).M
    def __invert__(self):        return self._e.__invert__().M
    def __lshift__(self, other): return self._e.__lshift__(other).M
    def __rshift__(self, other): return self._e.__rshift__(other).M
    def __or__(self, other):     return self._e.__or__(other).M
    def __xor__(self, other):    return self._e.__xor__(other).M
    def equivalent_to(self, other): return self._e.equivalent_to(other).M
    def __mod__(self, other):    return self._e.__mod__(other).M

    def __lt__(self, other):     return self._e.__lt__(other).M
    def __le__(self, other):     return self._e.__le__(other).M
    def __add__(self, other):    return self._e.__add__(other).M
    def __sub__(self, other):    return self._e.__sub__(other).M
    def __div__(self, other):    return self._e.__div__(other).M
    def __truediv__(self, other):return self._e.__truediv__(other).M
    def __floordiv__(self, other):return self._e.__floordiv__(other).M
    def __mul__(self, other):    return self._e.__mul__(other).M
    def __neg__(self):           return self._e.__neg__().M
    def __pos__(self):           return self._e.__pos__().M
    def __pow__(self, other):    return self._e.__pow__(other).M
    def __matmul__(self, other): return self._e.__matmul__(other).M

    def __radd__(self, other):    return self._e.__radd__(other).M
    def __rsub__(self, other):    return self._e.__rsub__(other).M
    def __rtruediv__(self, other): return self._e.__rtruediv__(other).M
    def __rfloordiv__(self, other): return self._e.__rfloordiv__(other).M
    def __rmul__(self, other):    return self._e.__rmul__(other).M
    def __rpow__(self, other):    return self._e.__rpow__(other).M
    def __rmatmul__(self, other): return self._e.__rmatmul__(other).M
    def __rmod__(self, other):    return self._e.__rmod__(other).M
    def __rand__(self, other):    return self._e.__rand__(other).M
    def __ror__(self, other):     return self._e.__ror__(other).M
    def __rxor__(self, other):    return self._e.__rxor__(other).M
    def __rrshift__(self, other): return self._e.__rrshift__(other).M
    def __rlshift__(self, other): return self._e.__rlshift__(other).M

    def __ge__(self, other):      return self._e.__ge__(other).M
    def __gt__(self, other):      return self._e.__gt__(other).M

    def __call__(self, *args):
        return self._e.__call__(*args)

    def __getitem__(self, other):
        # TypedExpr.__getitem__ is hardcoded to call the factory if its arg is a
        # TypedExpr, but we want to do this unconditionally (and never trigger
        # ordinary indexing code)
        return TypedExpr.factory('[]', self._e, other).M

    def __eq__(self, other):
        # python equality only -- necessary for this class to be hashable
        return self._e.__eq__(tenorm(other))

    def __hash__(self):
        return self._e.__hash__()

    # not implementable:
    # * the `in` operator force-converts to bool regardless of what __contains__
    #   returns
    # * the `len` operator requires __len__ to return an int

    # not hashable

    # do not want this class to be convertable to bool
    __bool__ = None

    def __repr__(self): return self._e.__repr__()
    def __str__(self): return self._e.__str__()
    def _repr_latex_(self): return self._e._repr_latex_()
    # def _repr_pretty_(self, p, cycle): return self._e._repr_pretty_(p, cycle)


class ApplicationExpr(TypedExpr):
    canonical_name = "Apply"
    def __init__(self, fun, arg, typ=None, defer=False, copying=False, **kwargs):
        if copying or defer:
            try:
                self.type = fun.type.right
            except AttributeError:
                # the input `fun` type is not itself functional, so we can't
                # even determine the output type. XX simple type placeholder?
                self.type = types.VariableType.any()
            super().__init__("Apply", fun, arg, defer=defer)
            return

        # this call may raise on OccursCheckFailure?
        ftype = get_type_system().unify_fun(fun.type, arg.type, typ)
        if ftype is None:
            raise TypeMismatch(fun, arg,
                error=f"Incompatible function-argument types `{fun.type}` and `{arg.type}`")
        f = self.type_constraint(fun, ftype, constant=True)
        a = self.type_constraint(arg, ftype.left, constant=True)
        history = f.type != fun.type or a.type != arg.type

        super().__init__("Apply", f, a, typ=ftype.right)

        if history:
            # bit of a hack: build a derivation with the deferred version as
            # the origin. Note: relies on derived not making a copy for this
            # case!
            derived(self, ApplicationExpr(fun, arg, defer=True),
                                    desc="Function-argument type inference")

        if isinstance(self[0], LFun):
            self[1].type_not_guessed()
        else:
            self.type_guessed = self[0].type_guessed

    def copy_core(self, other):
        other = super().copy_core(other)
        other.type_guessed = self.type_guessed
        return other

    def copy_local(self, fun, arg, **kwargs):
        # note: defer needs to be provided up front to the constructor
        return self.copy_core(
            ApplicationExpr(fun, arg, defer=self.defer, **kwargs))

    def latex_str(self, suppress_parens=False, **kwargs):
        # n.b. parens generated here never should be suppressed
        fun = self.args[0]
        arg = self.args[1]
        # suppress parens for Tuple args (among others)
        arg_str = f"({arg.latex_str(suppress_parens=True, **kwargs)})"
        if isinstance(fun, CustomTerm):
            return ensuremath(fun.custom_appl_latex(arg_str))
        elif isinstance(fun, LFun): # or maybe: not fun.term()?
            # we use [] for the parens, following the Heim & Kratzer convention.
            # (Is this really a good idea?)
            return ensuremath(f"{{[{fun.latex_str(suppress_parens=True, **kwargs)}]}}{arg_str}")
        else:
            return ensuremath(f"{fun.latex_str(**kwargs)}{arg_str}")

    def __repr__(self):
        fun = self.args[0]
        # ApplicationExpr can get things like ()(). (Any other cases?)
        arg_str = utils.parens(repr(self.args[1]),
            force=isinstance(self.args[1], ApplicationExpr))

        if isinstance(fun, CustomTerm):
            return fun.custom_appl(arg_str) # TODO: ???
        else:
            # assumption: LFun adds its own parens
            return f"{repr(fun)}{arg_str}"

    def try_coerce_new_argument(self, typ, remove_guessed=False,
                                                        assignment=None):
        """For guessed types, see if it is possible to coerce a new argument.
        Will recurse to find guessed types.

        This is not type inference.  Rather, it is a convenience shorthand for
        writing n-ary extensional predicates without type annotation."""
        if not self.type_guessed:
            return None
        result = self.args[0].try_coerce_new_argument(typ,
                                                        assignment=assignment)

        if result is not None:
            copy = ApplicationExpr(result, self.args[1], assignment=assignment)
            if (remove_guessed):
                result.type_guessed = False
            return copy
        else:
            return None

    def nucleus(self):
        # find the functional element at the center of potentially repeated
        # ApplicationExprs. Probably either an LFun or a TypedTerm. (Or a
        # Partial, Disjunction, ...)
        if is_te(self[0], ApplicationExpr):
            return self[0].nucleus()
        else:
            return self[0]

    def _compile(self):
        # XX this could use the AST to optimize further. Unclear whether the
        # optimizations are meaningful.
        # * uncurry an LFun and do all substs at once
        # * more precise vacuity checks. The check here is very simple, but
        #   could try to do something more syntactically complex. Right now it
        #   will miss something like (L x: L y: P(x))(a)(b). However, it might
        #   be a better use of time just to run the thing. The main function of
        #   skipping these cases is to avoid a KeyError if the assignment is
        #   incomplete for free terms in a discarded argument.
        # * ...?
        arg = self[1]._compiled
        if is_te(self[0], LFun) and self[0].vacuous():
            # if we can analytically determine that this ApplicationExpr
            # will discard the argument, don't bother calling it in the
            # compiled version. We do compile just for consistency of
            # error checking. As noted above, this misses a lot of cases.
            return lambda context: fun(context)(None)
        else:
            fun = self[0]._compiled

        from .meta import MetaTerm
        def c(context):
            f_exec = fun(context)
            # allows dicts/sets to act as functions. This could be pushed
            # to MetaTerm._compile but for now I prefer to leave the compiled
            # values as their actual python implementation.
            # XX don't do this dynamically?
            return MetaTerm._apply_impl(f_exec, arg(context))

        return c
        # # otherwise, fun should return a callable, use it:
        # return lambda context: fun(context)(arg(context))

    def _reduction_order(self):
        # prefer to reduce the argument before the function, in case the
        # argument is reused. (This is, however, non-optimal for constant fns)
        return (1,0)

    def meta_reducible(self):
        return self.args[0].meta() and is_concrete(self.args[1])

    def reducible(self):
        # XX disjunctive logic??
        return self.args[0].will_reduce(self.args[1])

    def reduce(self):
        """if there are arguments to op, see if a single reduction is
        possible."""
        if not self.reducible():
            return self
        else:
            result = self.args[0].apply(self.args[1])
            result.let = self.let
            return derived(result, self, desc="Reduction")

    def simplify(self, **sopts):
        # recursive reduction is not triggered locally, but rather via an
        # initial `reduce_all()` call. However, we do allow handling of
        # MetaTerms here via `evaluate`, triggerable independently from
        # reduction. (This can be useful when supplying MetaTerms via an
        # assignment.)
        # XX sequencing of this vs reduce is not ideal; if `reduce=True`
        # then an OutOfDomain case will crash before this code gets called.
        if get_sopt('evaluate', sopts) and self.meta_reducible():
            # _do_reduce should set a derivation
            return self._do_reduce(strict_charfuns=get_sopt('strict_charfuns', sopts))
        return self

    def calculate_partiality(self, vars=None, **sopts):
        # defer calculation of the argument until beta reduction has occurred
        # XX is this general enough?
        if isinstance(self.args[0], LFun) or isinstance(self.args[0], ApplicationExpr):
            return self
        else:
            return super().calculate_partiality(vars=vars, **sopts)

    @classmethod
    def random(self, random_ctrl_fun):
        from . import test
        ftyp = get_type_system().random_from_class(types.FunType)
        fun = test.random_lfun_force_bound(ftyp, random_ctrl_fun)
        arg = random_ctrl_fun(typ=ftyp.left)
        return ApplicationExpr(fun, arg)


class Tuple(TypedExpr):
    """TypedExpr wrapper on a tuple.

    This works basically as a python tuple would, and is indicated using commas
    within a parenthetical. `args` is a list containing the elements of the
    tuple."""

    canonical_name = "Tuple"

    def __init__(self, *args, typ=None, copying=False, **kwargs):
        ttype = types.TupleType(*[a.type for a in args])
        if not copying or typ is not None:
            ttype, _ = self.type_constraint(ttype, typ)
            args = [self.type_constraint(args[i], ttype[i], constant=True) for i in range(len(args))]

        super().__init__("Tuple", *args, typ=ttype)

    def _compile(self):
        # n.b. it is possible to more quickly access individual elements, but
        # this compiled function is intended to return an entire tuple
        # see TupleIndex._compile
        pre = tuple(a._compiled for a in self)
        return lambda context: tuple(a(context) for a in pre)

    def index(self, i):
        return self.args[i]

    def term(self):
        return False

    def tuple(self):
        """Return a python `tuple` version of the Tuple object."""
        return tuple(self.args)

    def __repr__(self):
        return "(" + ", ".join([repr(a) for a in self.args]) + ")"

    def latex_str(self, suppress_parens=False, **kwargs):
        inner = ", ".join([a.latex_str(**kwargs) for a in self.args])
        if not suppress_parens:
            inner = f"({inner})"
        return ensuremath(inner)

    def _repr_latex_(self):
        # override superclass behavior: always show outer parens for tuples
        return self.latex_str(suppress_parens=False)

    @classmethod
    def random(cls, ctrl, max_type_depth=1, max_tuple_len=5, allow_empty=True):
        if allow_empty:
            r = range(max_tuple_len+1)
        else:
            r = range(max_tuple_len+1)[1:]
        length = random.choice(r)
        signature = [get_type_system().random_type(max_type_depth, 0.5, allow_variables=False)
                                                        for i in range(length)]
        args = [ctrl(typ=t) for t in signature]
        return Tuple(*args)



# suppress any constant type
global suppress_constant_type
suppress_constant_type = False

# suppress only constant predicates
# a predicate type is either <e,t>, or any characteristic function of a set of
# tuples
global suppress_constant_predicate_type
suppress_constant_predicate_type = True

global suppress_bound_var_types
suppress_bound_var_types = True

class TypedTerm(TypedExpr):
    canonical_name = "TypedTerm"
    """used for terms of arbitrary type.  Note that this is not exactly
    standard usage of 'term'. In general, these cover variables and constants.
    The name of the term is 'op', and 'args' is empty.

    The attribute 'type_guessed' is flagged if the type was not specified; this
    may result in coercion as necessary."""
    def __init__(self, varname, typ=None, latex_op_str=None, assignment=None,
                                    defer_type_env=False, copying=False,
                                    validate_name=True, **kwargs):
        # NOTE: does not call super
        self.op = varname
        self.derivation = None
        self.defer = False
        self.let = False
        self._reduced_cache = []
        self.type_guessed = False

        # if the assignment provides some information about this term, we will
        # need to factor that in.
        if assignment is not None and self.op in assignment:
            self.from_assignment = assignment[self.op]
            self.let = self.from_assignment.let
        else:
            self.from_assignment = None

        if typ is None and self.from_assignment is None:
            # if there's no annotation on the term name, and no info from the
            # assignment, we can fall back on some default types for various
            # term names
            if not _allow_guessed_types:
                raise parsing.ParseError(f"No type provided for term `{self.op}` (guessed types disabled)")
            self.type = default_type(varname)
            self.type_guessed = True
        else:
            self.type = typ

        if not copying and not defer_type_env:
            # initialize a type environment based on self.type
            env = self.calc_type_env()

            # re-set the type, based on its value in the type env
            self.type = env.term_type(self.op, specific=True)
            self.set_type_env(env)

        self.suppress_type = False
        from .meta import MetaTerm
        if validate_name:
            if not isinstance(self.op, str):
                # note: don't use `s` parameter, because the resulting error
                # message is confusing for this specific case
                raise parsing.ParseError(
                    f"`TypedTerm` must have string operator name, got `{repr(self.op)}` (did you mean `MetaTerm`?)")

            if self.op.startswith("_"):
                raise parsing.ParseError(
                    "Invalid term name with `_` prefix for `TypedTerm` (did you mean `MetaTerm`?)",
                    s=repr(self.op))

            if not is_symbol(self.op):
                raise parsing.ParseError(
                    f"`TypedTerm` requires a valid symbol name, got `{self.op}`")

            # This follows the prolog convention: a named constant is a term with a
            # capitalized first letter. All MetaTerms are constants, 
            self._variable = is_var_symbol(self.op)
            self._constant = not self.variable

        self.args = list()
        self.latex_op_str = latex_op_str

    variable = property(operator.attrgetter('_variable'))
    constant = property(operator.attrgetter('_constant'))

    def copy(self):
        return self.copy_local(copying=True)

    def copy_core(self, other):
        other = super().copy_core(other)
        other.type_guessed = self.type_guessed
        other.from_assignment = self.from_assignment
        other.latex_op_str = self.latex_op_str
        return other

    def copy_local(self, copying=False, typ=None, **kwargs):
        # XX the type logic here is a bit convoluted.
        # * we don't want to build a type env until `from_assignment` is set,
        #   so constructor type env handling is deferred
        # * Type inference doesn't happen in the constructor for this class, so
        #   if a caller passes `typ` it needs to be handled here, rather than
        #   there. That is, `type` is essentially a *local* property for this
        #   class, unlike most others.
        # * copying=True cases explicitly need to copy the type env
        typ, _ = self.type_constraint(self.type, typ)
        result = TypedTerm(self.op, typ=typ, copying=copying, defer_type_env=True, **kwargs)
        result = self.copy_core(result)
        if copying:
            result.set_type_env(self.get_type_env().copy())
        return result

    def calc_type_env(self, recalculate=False):
        env = TypeEnv()

        if recalculate:
            # return a clean env with a copy of the old term mapping; this skips
            # type inference and removes all type var mappings from the picture
            env.term_mapping[self.op] = self.get_type_env().term_mapping[self.op]._clean_copy(self.type)
            env.update_var_set()
            return env
        elif self.from_assignment is not None:
            a_constraint = self.from_assignment.type
            if self.from_assignment.let:
                # if the assignment object is let-bound, explicitly add a type
                # binder to the constraint. This enables let-polymorphism via
                # the assignment
                a_constraint = types.Forall(a_constraint).normalize()
            env.add_term_mapping(self.op, a_constraint, allow_poly=True)

        if self.type is not None:
            env.add_term_mapping(self.op, self.type)

        # if we do not have a let-bound assignment value, don't store the
        # constraint for all posterity
        # (XX: is this right?)
        if self.from_assignment is not None and not (
                            self.from_assignment.let
                            or isinstance(self.from_assignment.type, types.Forall)):
            self.from_assignment = None
        return env

    def free_terms(self, var_only=False):
        if not var_only or self._variable:
            return {self.op}
        else:
            return set()

    def term(self):
        return True

    def _compile(self):
        # this is completely unsafe as to what `context` gives you; wrapper
        # functions in meta can be used to ensure type-safety.
        # XX should this at least use meta.compiled?
        # XX this does not do any sort of domain check on the context value
        return lambda context : context[self.op]

    def apply(self, arg):
        return self(arg)

    @property
    def term_name(self):
        return self.op

    def __repr__(self):
        return "%s_%s" % (self.op, repr(self.type))

    def should_show_type(self, assignment=None):
        if (assignment and suppress_bound_var_types
                        and not self.meta() and self.op in assignment):
            if self.type == assignment[self.op].type:
                return False
            # the false case can arise with let-polymorphism
        if self.suppress_type:
            return False
        if suppress_constant_type and self.constant and not self.meta():
            return False
        if suppress_constant_predicate_type and not self.meta():
            if (self.constant and self.type.functional()
                            and not self.type.is_polymorphic()):
                if ((self.type.left == types.type_e
                                or isinstance(self.type.left, types.TupleType))
                        and self.type.right == types.type_t):
                    return False
        return True

    def try_coerce_new_argument(self, typ, remove_guessed = False,
                                                            assignment=None):
        if not self.type_guessed:
            return None
        coerced_op = self.term_factory(self.op,
                                typ=types.add_internal_argument(self.type, typ),
                                preparsed=True)
        if not remove_guessed:
            coerced_op.type_guessed = True
        
        if coerced_op is not None and assignment is not None and self.op in assignment:
            # XX this seems like a dubious side effect...
            assignment[self.op] = coerced_op
        return coerced_op

    def __hash__(self):
        return hash("TypedTerm") ^ super().__hash__()

    def latex_str(self, show_types=True, assignment=None, superscript="", sf=False, **kwargs):
        if self.latex_op_str is None:
            op = self.op
        else:
            op = self.latex_op_str
        if sf:
            op = f"\\textsf{{{op}}}"
        if superscript:
            superscript = f"^{{{superscript}}}"
        if not show_types or not self.should_show_type(assignment=assignment):
            return ensuremath(f"{{{op}}}{superscript}")
        else:
            return ensuremath(f"{{{op}}}{superscript}_{{{self.type.latex_str()}}}")

    random_term_base = {types.type_t : "p", types.type_e : "x", types.type_n : "n"}
    atomics = {types.type_t, types.type_e, types.type_n}

    @classmethod
    def random(cls, random_ctrl_fun, typ=None, blockset=None, usedset=set(),
                            prob_used=0.8, prob_var=0.5, max_type_depth=1):
        ts = get_type_system()
        if blockset is None:
            blockset = set()
        varname = None
        is_var = (random.random() <= prob_var)
        try_used = ((len(usedset) > 0) and (random.random() <= prob_used))
        if typ is None:
            if try_used:
                used_var = random.choice(list(usedset))
                varname = used_var.op
                typ = used_var.type
            else:
                typ = ts.random_type(max_type_depth, 0.5)
        else:
            used_typed = [x for x in list(usedset)
                                if (x.type==typ and x.variable == is_var)]
            if try_used and len(used_typed) > 0:
                varname = (random.choice(list(used_typed))).op
        if varname is None:
            if not is_var and typ in cls.atomics and random.choice([True, False]):
                # when possible, on a coinflip choose type domain element
                # instead of a regular term constant
                varname = typ.domain.random()
            else:
                if typ in cls.random_term_base.keys():
                    base = cls.random_term_base[typ]
                else:
                    base = "f"
                if not is_var:
                    base = base.upper()
                varname = alpha_variant(base, blockset | {n.op for n in usedset})
        
        return TypedExpr.term_factory(varname, typ=typ)


class CustomTerm(TypedTerm):
    """A subclass of TypedTerm used for custom displays of term names.

    The main application is for English-like metalanguage a la Heim and Kratzer.
    This isn't fully implemented as that metalanguage is actually extremely
    difficult to get right computationally..."""
    def __init__(self, varname, custom_english=None, suppress_type=True,
                 small_caps=True, **kwargs):
        TypedTerm.__init__(self, varname, **kwargs)
        self.custom = custom_english
        self.sc = small_caps
        self.suppress_type = suppress_type
        self.verbal = False
        # TODO: check type against custom string

    def copy(self):
        return self.copy_core(CustomTerm(self.op, custom_english=self.custom,
                                   suppress_type=self.suppress_type,
                                   small_caps=self.sc,
                                   typ=self.type))

    def copy_local(self, **kwargs):
        return self.copy()

    def copy(self, op):
        return self.copy_core(CustomTerm(op, custom_english=self.custom,
                              suppress_type=self.suppress_type,
                              small_caps=self.sc,
                              typ=self.type))

    def latex_str(self, show_types=True, **kwargs):
        s = ""
        # custom made small caps
        if self.sc:
            if len(self.op) == 1:
                s += "{\\rm %s}" % (self.op[0].upper())
            else:
                s += "{\\rm %s {\\small %s}}" % (self.op[0].upper(),
                                                        self.op[1:].upper())
        else:
            s += "{\\rm %s}" % self.op
        if show_types and not self.suppress_type:
            s += "_{%s}" % self.type.latex_str()
        return ensuremath(s)

    def __repr__(self):
        if self.sc:
            return self.op.upper()
        else:
            return self.op

    def get_custom(self):
        # needs to be dynamic to deal with coerced types
        if self.custom is None:
            if self.type == types.type_property:
                if self.verbal:
                    return "s"
                else:
                    return "is a"
            else:
                if self.type == types.type_transitive:
                    if self.verbal:
                        return "s"
                return ""
        else:
            return self.custom


    def custom_appl_latex(self, arg_str):
        if self.verbal:
            return "%s\\text{ }%s\\text{%s}" % (arg_str, self.latex_str(),
                                                            self.get_custom())
        else:
            return "%s \\text{ %s }%s" % (arg_str, self.get_custom(),
                                                            self.latex_str())

    def custom_appl(self, arg_str):
        if self.verbal:
            return "%s %s%s" % (arg_str, self.latex_str(), self.get_custom())
        else:
            return "%s %s %s" % (arg_str, repr(self), self.get_custom())



###############
#
# Partiality
#
###############

# possibly these belong in boolean, or somewhere else?

class Partial(TypedExpr):
    canonical_name = "Partial"
    def __init__(self, body, condition, typ=None, **kwargs):
        if condition is None:
            condition = from_python(True)

        condition = self.type_constraint(condition, types.type_t, constant=True)
        body, typ = self.type_constraint(body, typ)

        super().__init__("Partial", body, condition, typ=typ)

    @property
    def body(self):
        return self[0]

    @property
    def condition(self):
        return self[1]

    def undefined(self):
        # note: returning True doesn't mean defined!
        if isinstance(self.condition, Partial):
            return self.condition.undefined()
        else:
            return self.condition == False

    def calculate_partiality(self, vars=None, **sopts):
        result = self
        new_condition = self.condition
        new_body = result.body.calculate_partiality(vars=vars, **sopts)
        # XX this derivation is a bit clunky
        while isinstance(new_body, Partial):
            new_condition = derived(new_condition & new_body.condition,
                new_condition,
                "Partiality (merge conditions from body)")
            new_body = derived(new_body.body.copy(), new_body,
                "Partiality (remove conditions from body)")

        new_condition = new_condition.calculate_partiality(vars=vars)
        # in the next steps, we make a copy of the condition/body, but use the
        # uncopied version as a subexpression. This gives the derivation for
        # simplify_all() below a clean slate and shows the partiality calculation
        # steps only once.
        if new_condition is not self.condition:
            result = derived(result.subst(1, new_condition.copy()), result,
                    desc=f"Partiality calculation (recursion on {result.name_of(1)})",
                    subexpression=new_condition)

        if new_body is not result.body:
            result = derived(result.subst(0, new_body.copy()), result,
                    desc=f"Partiality calculation (recursion on {result.name_of(0)})",
                    subexpression=new_body)

        return result.simplify_all(**sopts)

    def __eq__(self, other):
        if self.undefined() and isinstance(other, Partial):
            return other.undefined()
        else:
            return super().__eq__(other)

    def __hash__(self):
        if self.undefined():
            # identical to superclass __hash__, except the dummy None value in
            # the body slot
            from .boolean import false_term
            return hash(self.op) ^ hash((None, false_term)) ^ hash(self.type)
        else:
            return super().__hash__()

    def _compile(self):
        # err = f"Condition failed on compiled `{repr(self)}`"
        body = self[0]._compiled
        cond = self[1]._compiled
        from .meta import DomainError
        # XX this error message is not particularly clear
        err = DomainError(self[0], self, f"Condition failed on compiled `Partial`")
        def c(context):
            if not cond(context):
                # XX revisit at some point
                raise err
            return body(context)
        return c

    def _reduction_order(self):
        if self[1] == True:
            return super()._reduction_order()
        else:
            # do not reduce the body at all if the condition is not True. Note
            # that simplify_point for this class can restart reduction, if
            # reduce=True.
            return (1,)

    def simplify(self, **sopts):
        if self.condition == True:
            # the copy here is (apparently) needed to get derivation bookkeeping right...
            return derived(self.body.copy(), self, "Partiality elimination")
        return self

    def name_of(self, i):
        if i == 0:
            return "partiality body"
        else:
            return "condition"

    def simplify_point(self, pre=False, **sopts):
        # for Partial, we want to simplify first the condition, then the body.
        # this requires messing with simplification internals in a complex way,
        # unfortunately.

        result = self
        new_condition = result[1].simplify_all(**sopts)
        if new_condition is not result[1]:
            result = derived(result.subst(1, new_condition), result,
                    desc=f"Recursive simplification of {result.name_of(1)}",
                    subexpression=new_condition)

        evaluate = get_sopt('evaluate', sopts)
        sreduce = get_sopt('reduce', sopts)

        if new_condition != True:
            # do not evaluate the body if the expression has not resolved to
            # True (e.g. if it is unsimplified, or undefined). (Perhaps,
            # if the condition is False, the body shouldn't even be simplified?
            # another approach would be to simply replace the body with a
            # different TyepdExpr that implemented non-simplification.)
            sopts['evaluate'] = False
            sopts['reduce'] = False
        # otherwise, this call may trigger a reduce_all step
        new_body = result[0].simplify_all(**sopts)
        if new_body is not result[0]:
            result = derived(result.subst(0, new_body), result,
                    desc=f"Recursive simplification of {result.name_of(0)}",
                    subexpression=new_body)
        sopts['evaluate'] = evaluate
        sopts['reduce'] = sreduce
        result = result.simplify(**sopts)
        return result

    def term(self):
        return self.body.term()

    def tuple(self):
        return tuple(self.args)
    
    def meta_tuple(self):
        return Tuple(*self.args)
    
    def __repr__(self):
        return f"Partial({repr(self.body)}, {repr(self.condition)})"
        
    def latex_str(self, suppress_parens=False, **kwargs):
        body_str = self.body.latex_str(suppress_parens=True, **kwargs)
        if self.condition == False:
            # XX \xcancel works in current MathJax, but it seems likely that it
            # won't work elsewhere...
            body_str = f"\\xcancel{{{body_str}}}"
        condition_str = self.condition.latex_str(suppress_parens=True, **kwargs)
        return ensuremath(f"\\left|\\begin{{array}}{{l}}{body_str}\\\\{condition_str}\\end{{array}}\\right|")

    @classmethod
    def get_condition(cls, p):
        if isinstance(p, Partial):
            return p.condition
        else:
            return from_python(True)
        
    @classmethod
    def get_atissue(cls, p):
        if isinstance(p, Partial):
            return p.body
        else:
            return p

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        # This will implicitly use the same depth for the body and condition
        typ = get_type_system().random_type(max_type_depth, 0.5)
        body = ctrl(typ=typ)
        condition = ctrl(typ=types.type_t)
        return Partial(body, condition)

        
class Body(TypedExpr):
    canonical_name = "Body"
    def __init__(self, body, typ=None, **kwargs):
        body, typ = self.type_constraint(body, typ)
        super().__init__("Body", body, typ=typ)

    def _compile(self):
        if isinstance(self[0], Partial):
            pre = self[0].body._compiled
        else:
            pre = self[0]._compiled
        return lambda context: pre(context)

    def calculate_partiality(self, vars=None, **sopts):
        result = self[0].calculate_partiality(vars=vars, **sopts)
        intermediate = derived(Body(result), self, "Partiality calculation (recursion on Body)",
            subexpression=result)
        if isinstance(result, Partial):
            return derived(result.body.copy(), intermediate, "Body extraction")
        else:
            return derived(result, intermediate, "Body extraction (trivial)")

    def __repr__(self):
        return f"Body({repr(self[0])})"

    def latex_str(self, suppress_parens=False, **kwargs):
        body_str = self[0].latex_str(suppress_parens=True, **kwargs)
        return ensuremath(f"\\textsf{{Body}}({body_str})")


class Condition(TypedExpr):
    canonical_name = "Condition"
    def __init__(self, body, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        super().__init__("Condition", body, typ=typ)

    def _compile(self):
        if isinstance(self[0], Partial):
            pre = self[0].condition._compiled
            return lambda context: pre(context)
        else:
            return lambda context: True

    def calculate_partiality(self, vars=None, **sopts):
        from .boolean import true_term
        result = self[0].calculate_partiality(vars=vars, **sopts)
        intermediate = derived(Condition(result), self, "Partiality calculation (recursion on Condition)",
            subexpression=result)
        if isinstance(result, Partial):
            return derived(result.condition.copy(), intermediate, "Condition extraction")
        else:
            return derived(true_term, intermediate, "Condition extraction (trivial)")

    def __repr__(self):
        return f"Condition({repr(self[0])})"

    def latex_str(self, suppress_parens=False, **kwargs):
        body_str = self[0].latex_str(suppress_parens=True, **kwargs)
        return ensuremath(f"\\textsf{{Condition}}({body_str})")


def pcond(t):
    from .boolean import true_term
    if isinstance(t, Partial):
        return t.condition
    else:
        return true_term


def pbody(t):
    if isinstance(t, Partial):
        return t.body
    else:
        return t


def partial(body, *conditions, force=False):
    from .boolean import BinaryAndExpr
    conditions = [c for c in conditions if c != True]
    if conditions or force:
        return Partial(body, BinaryAndExpr.join(conditions))
    else:
        return body


###############
#
# more type underspecification
#
###############


# The `Disjunctive` class allows for the construction of ad-hoc polymorphic
# expressions in the  metalanguage. It takes a set of expressions, and gives you
# an object that will simplify  to one or more of the expressions depending on
# type adjustment/inference.  It enforces the constraint that every (non-
# disjunctive) type it is constructed from must be simplifiable to no more than
# one expression.  So, constructing a Disjunctive from two objects of the same
# type is not permitted, but neither are cases where the types overlap (so for
# example,  where you have an expression of type e, and an expression of type
# [e|t], because that would lead to a problem if it were adjusted to type e.)
class Disjunctive(TypedExpr):
    canonical_name = "Disjunctive"
    def __init__(self, *disjuncts, typ=None, **kwargs):
        if len(disjuncts) == 0:
            raise parsing.ParseError("Empty Disjunction not allowed")
        elif len(disjuncts) == 1:
            principal = disjuncts[0].type
        else:
            principal = types.DisjunctiveType(*[d.type for d in disjuncts])
        typ, _  = self.type_constraint(principal, typ)

        # need to check for duplicates across expressions
        all_types = set()
        live = []
        for d in disjuncts:
            d, _ = self.type_constraint(d, typ, error=False)
            if d is None:
                continue
            live.append(d)
            dt = d.type
            if not isinstance(dt, types.DisjunctiveType):
                dt = [dt]
            for t in dt:
                if t in all_types:
                    raise parsing.ParseError(
                        "Disjoined expressions must determine unique types"
                        f" (type `{t}` appears duplicated in expression `{repr(d)}`")
                else:
                    all_types.add(t)

        if len(live) == 0:
            raise parsing.TypeMismatch(principal, typ,
                "Type constraints resulted in empty Disjunction")

        super().__init__("Disjunctive", *live, typ=typ)
    
    def simplify(self, **kwargs):
        if len(self) == 1:
            return derived(self[0], self, "Trivial Disjunction")
        else:
            return self

    def term(self):
        return False
    
    def __repr__(self):
        return "Disjunctive(%s)" % (",".join([repr(a) for a in self.args]))
    
    def latex_str(self, disj_type=False, suppress_parens=False, **kwargs):
        if disj_type:
            return ensuremath("{Disjunctive}^{%s}(%s)" % (self.type.latex_str(),
                     ", ".join([a.latex_str(**kwargs) for a in self.args])))
        else:
            return ensuremath("{Disjunctive}(\\left[%s\\right])"
                    % (("\\mid{}").join([a.latex_str(**kwargs)
                                                        for a in self.args])))
    
    def try_adjust_type_local(self, unified_type, derivation_reason, env):
        # class-specific behavior: if type adjustment results in a non-disjunctive
        # type, return only the disjunct
        with no_derivations():
            return self.copy_local(*self, typ=unified_type).simplify()

    def apply(self, arg):
        if not self.type.functional():
            raise TypeMismatch(self, arg,
                        error="Application to a non-functional Disjunction")
        applied_disjuncts = list()
        for d in self.args:
            if not d.functional():
                continue
            try:
                applied_disjuncts.append(d.apply(arg))
            except TypeMismatch:
                continue
        result = self.factory(*applied_disjuncts)
        if result is None:
            raise TypeMismatch(self,arg,
                        error="Application to a non-functional Disjunction")
        return result

    @classmethod
    def factory(cls, *disjuncts):
        disjuncts = set(disjuncts)
        if len(disjuncts) == 0:
            return None
        elif len(disjuncts) == 1:
            (r,) = disjuncts
            return r
        else:
            return Disjunctive(*disjuncts)

    @classmethod
    def random(cls, ctrl, max_type_depth=1, max_disj_len=3):
        r = range(max_disj_len+1)[1:]
        length = random.choice(r)
        signature = {get_type_system().random_type(max_type_depth, 0.5,
                            allow_variables=False, allow_disjunction=False)
                        for i in range(length)}
        args = [ctrl(typ=t) for t in signature]
        return cls.factory(*args) # may not actually generate a Disjunctive


# TODO: convert to a binary operator, or allow n-ary operators, so that this
# can be in the registry
TypedExpr.add_local("Disjunctive", Disjunctive)


###############
#
# Operators
#
###############


class SyncatOpExpr(TypedExpr):
    """This class abstracts over expressions headed by n-ary operators.

    In logical terms, this corresponds to syncategorematic definitions of
    operators as is standard in definitions of logics. For example, statements
    like '~p is a sentence iff p is a sentence'.

    It should not be instantiated directly."""

    arity = 2
    canonical_name = None
    secondary_names = set()
    op_name_uni = None
    op_name_latex = None
    commutative = False # default - override if needed
    associative = False # default - override if needed. Mostly only relevant if
                        # the arguments have the same type as `typ`.
    operator_style = True # if unary, do we omit parens?
    infix_style = True # if 2-ary, is it infix or prefix?
    # `latex_operator_style` and `latex_infix_style` can be set independently
    # of the above two, but otherwise, will inherit their values

    # is the operation left associative without parens, i.e. for arbitrary `@`
    # does `p @ q @ r` mean `((p @ q) @ r)`?
    # this is currently just cosmetic, in that it suppresses parens for left
    # recursion on rich reprs. Essentially all python operations are left
    # associative, and the metalanguage operators inherit this behavior, so
    # it is true by default. But you could set it to False to always show
    # for some operation.
    left_assoc = True # currently just cosmetic: suppresses parens for left recursion

    def __init__(self, arg_type, *args, typ=None, tcheck_args=True):
        if typ is None:
            typ = arg_type # convenient, but somewhat arbitrary, default
        if tcheck_args:
            args = [self.type_constraint(a, arg_type, constant=True) for a in args]
        super().__init__(self.canonical_name, *args)
        self.type = typ
        if self.op_name_uni is None:
            self.op_name_uni = self.op
        # shadow the class var:
        if self.op_name_latex is None:
            self.op_name_latex = self.op_name_uni

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, **kwargs):
        """This must be overriden by classes that are not produced by the
        factory."""
        return self.copy_core(op_expr_factory(self.op, *args, **kwargs))

    def name_of(self, i):
        return f"operand {i}"

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text("%s(...)" % self.op_name_uni)
        elif self.arity == 1:
            p.text(self.op_name_uni)
            if not self.operator_style:
                p.text("(")
            p.pretty(self.args[0])
            if not self.operator_style:
                p.text(")")
        else:
            if self.infix_style:
                # XX left assoc parens?
                p.text("(")
                for a in self.args[0:-1]:
                    p.pretty(self.args[0])
                    p.text(" %s " % self.op_name_uni)
                p.pretty(self.args[-1])
                p.text(")")
            else:
                p.text("%s" % self.op_name_uni)
                p.text("(")
                for a in self.args[0:-1]:
                    p.pretty(self.args[0])
                    p.text(", ")
                p.pretty(self.args[-1])
                p.text(")")

    def _sub_latex_str(self, i, suppress_parens = False, **kwargs):
        from .sets import SetEquivalence
        if (self.left_assoc
                        and len(self.args) == 2 and i == 0
                        # stylistic choice: only drop parens for cases where order doesn't matter
                        and commutative(self) and associative(self)
                        and isinstance(self.args[i], self.__class__)
                # suppress parens for simple equality expressions, i.e. ones
                # that do not involve recursion. This excludes logical <=>
                # which is covered by the above case.
                or (isinstance(self.args[i], BinaryGenericEqExpr)
                        or isinstance(self.args[i], SetEquivalence))
                    and self.args[i].term_parent()):
            suppress_parens = True
        return self.args[i].latex_str(suppress_parens=suppress_parens, **kwargs)

    def latex_str(self, suppress_parens=False, **kwargs):
        if self.arity == 1:
            latex_operator_style = getattr(self, 'latex_operator_style', self.operator_style)
            # XX allow for latex postfix rendering? (Possibly a bad idea given
            # that this syntax doesn't exist at all in the metalanguage...)
            if (latex_operator_style):
                return ensuremath("%s %s" % (self.op_name_latex,
                    self._sub_latex_str(0, **kwargs)))
            else:
                return ensuremath("%s(%s)" % (self.op_name_latex,
                    self._sub_latex_str(0, suppress_parens=True, **kwargs)))
        else:
            latex_infix_style = getattr(self, 'latex_infix_style', self.infix_style)
            if latex_infix_style:
                sub_parens = True
                inner = f" {self.op_name_latex} ".join(
                    [self._sub_latex_str(i, **kwargs) for i in range(len(self.args))])
                if not suppress_parens:
                    inner = f"({inner})"
                return ensuremath(inner)
            else:
                arg_str = ", ".join(a.latex_str(suppress_parens=True, **kwargs) for a in self.args)
                return ensuremath(f"{self.op_name_latex} ({arg_str})")

    @classmethod
    def join(cls, l, empty=None, assoc_right=False):
        """Joins an arbitrary number of arguments using the binary operator.
        Requires a subclass that defines a two-parameter __init__ function.

        Will also fail on operators that do not take the same type (i.e.
        SetContains).
        """
        if cls.arity != 2:
            raise ValueError("Can't join with a %d-ary operator", cls.arity)
        if empty is None:
            empty = from_python(True)
        if len(l) == 0:
            return empty
        if len(l) == 1:
            return l[0].copy()
        elif assoc_right:
            cur = l[-1]
            for i in range(len(l) - 1, 0, -1):
                cur = cls(l[i - 1], cur)
            return cur
        else:
            # left associativity is a bit more annoying, but it matches the
            # default associativity of operators like & and | in python
            cur = l[0]
            for i in range(len(l) - 1):
                cur = cls(cur, l[i+1]) # will raise an error if the subclass
                                       # doesn't define a constructor this way.
            return cur

    @classmethod
    def random(cls, ctrl):
        # this will fail if type_t is wrong for the class, so override
        return cls(*[ctrl(typ=types.type_t) for a in range(cls.arity)])


def to_python(te):
    if te.op in te.type.domain:
        return te.op
    else:
        return te


def from_python(p, typ=None):
    # generalize me
    from .boolean import true_term, false_term
    # normalize True and False to the singleton instances, in order to make
    # display customization simpler
    # use `is` instead of `==` because 0/1 compare equal to False/True
    if p is True and (typ is None or typ == types.type_t):
        return true_term
    elif p is False and (typ is None or typ == types.type_t):
        return false_term
    else:
        # this will raise if there is no known type domain for python objects
        # of p's type
        from .meta import MetaTerm
        # should these cases be handled in MetaTerm?
        if isinstance(p, collections.abc.Mapping):
            p = utils.frozendict(p)
        elif isinstance(p, collections.abc.Set):
            p = frozenset(p)
        return MetaTerm(p, typ=typ)


def from_python_container(p, default=None):
    """Construct a TypedExpr given a (potentially recursive) python set/tuple
    of TypedExpr objects. This normalizes `tuple` to `Tuple`, `set` to
    `ListedSet`, and `dict` to `MapFun`.

    Quirk relative to python: in order to get a set-theoretic interpretation
    for `{}`, the empty dict is treated as an empty set at an unknown type."""
    from .sets import sset
    if isinstance(p, tuple): # or collections.abc.Sequence
        # should an empty tuple force a MetaTerm?
        return Tuple(*tuple(from_python_container(elem, default=elem) for elem in p))
    elif isinstance(p, collections.abc.Set):
        return sset((from_python_container(elem, default=elem) for elem in p))
    elif isinstance(p, dict) and len(p) == 0:
        # empty dict is treated as empty set, so that `{}` has its expected
        # mathematical meaning
        return sset(set())
    elif isinstance(p, dict):
        p = {from_python_container(k, default=k):
                from_python_container(p[k], default=p[k]) for k in p}
        if (all(k.meta() and p[k].meta() for k in p)):
            from .meta import MetaTerm
            return MetaTerm(p)
        else:
            return MapFun.from_dict(p)

    return tenorm(default)


def is_concrete(s):
    """Is `s` a MetaTerm, or a finite data structure consisting only of MetaTerms?"""
    from .sets import ListedSet
    return (s.meta()
        or (is_te(s, ListedSet) or is_te(s, Tuple))
            and all(is_concrete(elem) for elem in s))


def to_python_container(e, default=None):
    """Convert a (listed) set / tuple object, potentially recursively, into
    a corresponding python container."""
    from .sets import ListedSet
    if isinstance(e, ListedSet) or e.meta() and isinstance(e.type, types.SetType):
        return frozenset({to_python_container(elem, default=elem) for elem in e.set()})
    elif isinstance(e, Tuple) or e.meta() and isinstance(e.type, types.TupleType):
        return tuple(to_python_container(elem, default=elem) for elem in e.tuple())
    # handling for MetaTerm functions that have a set/dict implementation?

    return default


def to_concrete(s, strict=False):
    """Generate a normal form for metalanguage sets/tuples that allows for
    comparison across different ways of constructing them (meta and non-meta).
    ListedSets, Tuples, and the MetaTerm variants thereof will be converted
    (recursively) to frozenset/tuple objects, with non-convertable TypedExpr
    elements at the bottom of this. If `strict` is true, this will raise
    a ValueError on `s` parameters that are not fully concrete. This function
    accepts python Set/Sequence objects for `s` as well, and is idempotent.
    With `strict`=False, this is essentially a wrapper on to_python_container
    with the idempotency addition.

    If there are somehow embedded sets/tuples within a non-convertable part
    of `s`, this will not recurse to normalize them.

    See also
    --------
    is_concrete
    """
    # XX the recursive part of this is not very efficient
    if is_te(s):
        c = to_python_container(s)
        if c is None:
            if s.meta() or not strict:
                return s
            else:
                raise ValueError(f"Can't convert expression to concrete container: `{s}`")
        return to_concrete(c, strict=strict)
    elif isinstance(s, collections.abc.Set):
        return frozenset({to_concrete(elem, strict=strict) for elem in s})
    elif isinstance(s, collections.abc.Sequence):
        return tuple(to_concrete(elem, strict=strict) for elem in s)
    else:
        raise ValueError(f"Can't convert expression to concrete: `{s}`")


# decorator for wrapping simplify functions, see examples in `meta.number`.
# TODO: this could be generalized a further...
def op(op, arg_type, ret_type,
            op_uni=None, op_latex=None, deriv_desc=None,
            python_only=True):
    if deriv_desc is None:
        deriv_desc = op_uni and op_uni or op

    def op_decorator(func):
        # we will pass `self` to func, so allow an extra param for it
        op_arity = len(inspect.signature(func).parameters) - 1

        # constructs a subclass of either Syncat
        if not (op_arity == 1 or op_arity == 2):
            raise ValueError(f"@op needs function of arity 1 or 2 (got {op_arity})")
        class WrappedPyOp(SyncatOpExpr):
            arity = op_arity
            canonical_name = op
            op_name_uni = op_uni
            op_name_latex = op_latex

            def __init__(self, *args, typ=None, **kwargs):
                # XX this updates __name__ but not __class__
                functools.update_wrapper(self, func)
                if len(args) != self.arity:
                    # call superclass without type checking so that the op
                    # name is set correctly
                    super().__init__(arg_type, *args, typ=ret_type, tcheck_args=False)
                    # what exception type to use here?
                    raise parsing.ParseError(
                        f"Operator `{self.op_name_uni}` ({func.__name__}) needs {self.arity} operands but {len(args)} were given")
                # would order ever matter here?
                typ, _ = self.type_constraint(ret_type, typ)
                self.operator_style = True
                super().__init__(arg_type, *args, typ=typ)

            def _compile(self):
                # this could be faster if it weren't generic
                args = tuple(a._compiled for a in self)
                return lambda context: func(self, *[a(context) for a in args])

            def simplify(self, **sopts):
                parts = [to_python(a.copy()) for a in self.args]
                if python_only and any([isinstance(a, TypedExpr) for a in parts]):
                    return self
                result = func(self, *parts)
                if result is self:
                    return self
                # XX is `te` really the right thing to call here?
                return derived(te(result), self, desc=deriv_desc)

            @classmethod
            def random(cls, ctrl):
                args = [ctrl(typ=arg_type) for i in range(cls.arity)]
                return cls(*args)

        # some metaprogramming to get nicer reprs for the class object. If we
        # don't overwrite these, the repr will show something like:
        # `lamb.meta.core.op.<locals>.op_decorator.<locals>.WrappedPyOp`,
        # which is of course completely unhelpful. The builtin (C) repr for
        # `type` uses specifically __module__ and __qualname__. Because `func`
        # here is the decorated function, using its `__qualname__` gets the
        # exact right reference to the class produced, e.g.
        # `lamb.meta.boolean.UnaryNegExpr`. (An alternative here that might be
        # clearer would be to use a metaclass; but as of py3.3 I don't think
        # the python internals this is relying on are likely to change...)
        WrappedPyOp.__name__ = func.__name__
        WrappedPyOp.__qualname__ = func.__qualname__
        WrappedPyOp.__module__ = func.__module__
        return WrappedPyOp
    return op_decorator


# probably belongs elsewhere
class BinaryGenericEqExpr(SyncatOpExpr):
    canonical_name = "<=>"
    secondary_names = {"==", "%"}
    op_name_latex = "="
    commutative = True
    # note: this associativity here is fairly in principle, since it only
    # applies at type t, and type t has a special case implementation in a
    # different class...
    associative = True

    # because of load sequencing issues, arg_signature is initialized in __init__.py
    # arg_signature = tp("(X,X)")

    """Type-generic equality.  This places no constraints on the type of `arg1`
    and `arg2` save that they be equal."""
    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, types.type_t, constant=True)
        # Could even generalize this to handle args of completely arbitrary
        # types
        arg1, arg2 = self.type_constraint(arg1, arg2,
                                error="Equality requires compatible types")
        super().__init__(arg1.type, arg1, arg2, typ=typ, tcheck_args = False)

    def _compile(self):
        # XX is this safe to implement at every type?
        if self[0] == self[1]:
            # if we have syntactic identity, that guarantees equivalence even
            # without execution.
            # XX it's a bit weird that functions will work iff they meet this
            # criteria...
            return lambda context: True
        l = self[0]._compiled
        r = self[1]._compiled
        def c(context):
            left = l(context)
            right = r(context)
            # can this be done statically?
            if callable(left) and callable(right):
                raise TypeError(f"Unable to dynamically check equality for {left} <=> {right}")
            return left == right
        return c

    def simplify(self, **sopts):
        # TODO: if simplification results in this having a boolean or set type
        # fall back on specializations. (How to do this in a sufficiently
        # generalized way?)
        if (is_concrete(self[0]) and is_concrete(self[1])):
            # for any fully concrete sets/tuples, we should use the compiled
            # implementation
            from .meta import exec, MetaTerm
            return derived(MetaTerm(exec(self)), self, desc="Equality")
        elif self.args[0] == self.args[1]:
            from .boolean import true_term
            # *heuristic* simplification rule: under syntactic equivalence,
            # simplify `p == p` to just `true`.
            return derived(true_term, self, desc="Equality")
        else:
            return self # this would require a solver for the general case

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        body_type = get_type_system().random_type(max_type_depth, 0.5)
        return cls(ctrl(typ=body_type), ctrl(typ=body_type))


class TupleIndex(SyncatOpExpr):
    arity = 2
    canonical_name = "[]" # not a normal SyncatOpExpr!
    commutative = False

    def __init__(self, arg1, i, typ=None, valid_indices=None, copying=False, **kwargs):
        # this constructor is overall quite complicated because it allows for
        # variables in the index slot and the tuple slot. Because of the latter,
        # assuming that `arg1` supports the tuple api isn't safe. We do require
        # that its type be a TupleType. (Variable types on the left are not
        # supported!)
        # XX support metalanguage slicing?
        self.type_constraint(arg1.type, types.TupleType, constant=True)

        if valid_indices is None:
            # by default: all indices for the tuple are valid
            self._valid_indices = range(-len(arg1.type), len(arg1.type))
        else:
            self._valid_indices = valid_indices

        if copying:
            if typ is None:
                raise ValueError("Bug: TupleIndex copying requires `typ` to be specified")
            super().__init__(typ, arg1, i, tcheck_args=False)
            return

        i = self.type_constraint(i, types.type_n, constant=True)
        # type constraint call ensures that any bare ints are wrapped

        # minimally init self.args
        super().__init__(None, arg1, i, tcheck_args=False)

        raw_i = self.resolve_index()
        if raw_i is not None:
            # concrete index
            self._valid_indices = {raw_i, raw_i - len(arg1)}
            output_type, _ = self.type_constraint(arg1.type[raw_i], typ)
            if output_type != typ:
                # we need to adjust the tuple based on index i
                sig = list(arg1.type.signature)
                sig[raw_i] = output_type
                ttype = types.TupleType(*sig)
                # XX is this constant?
                arg1, ttype = self.type_constraint(arg1, ttype)
        elif typ is not None:
            # non-concrete index, but a type constraint is being imposed. We
            # need to filter valid indices by whether anything matches the
            # type constraint.
            sig = [self.type_constraint(t, typ, error=False)[0] for t in arg1.type]
            self._valid_indices = {j for j in self._valid_indices if sig[j] is not None}
            # this couldn't be handled in the fallthrough, but it's useful to
            # specifically error here given that we know `typ` was provided
            if not self._valid_indices:
                raise TypeMismatch(arg1, typ,
                    error=f"No possible tuple elements for index `{repr(i)}` that match type requirement")
            for j in range(len(sig)):
                if sig[j] is None:
                    # ignore types at non-matching indices
                    # XX this is an extremely heavy way to go about this
                    sig[j] = types.VariableType.any()
            # update self.args[0] in place with any necessary type adjustments
            self.args[0], _ = self.type_constraint(arg1, types.TupleType(*sig))
        # else case: index is not concrete, and no type constraint is provided
        # to the constructor. The output type is determined entirely by the
        # `resolve_type()` call below, and may be ∀X. See comment in
        # that function.

        self.type = self.resolve_type()
        if self.type is None:
            # this shouldn't be very easy to reach
            raise TypeMismatch(arg1, i,
                error=f"No possible tuple elements in indices {repr(self._valid_indices)}")


    def resolve_index(self, i=None):
        if i is None:
            i = self[1]
        if i.meta():
            # this effectively enforces an undeclared subtype of type_n
            # based on the range check. Note: this subtyping effect does *not*
            # participate in type inference!
            raw_i = i.op
            if raw_i not in self._valid_indices:
                from .meta import MetaIndexError
                if isinstance(raw_i, int):
                    if raw_i in range(len(self[0].type)):
                        # it would be nice to show the type here, but the order
                        # of operations makes it hard
                        err = f"Tuple indexing with index that doesn't meet type constraints`"
                    else:
                        err = "Tuple indexing with out-of-range index"
                else:
                    err = "Tuple indexing with invalid index"
                # raise a DomainError on analogy with partial functions / Iota
                # XX the resulting messages aren't very good
                raise MetaIndexError(i, self[0], extra=err)
            # note! the above check should protect against both IndexError and
            # TypeError for the following indexings. If it doesn't this is a
            # bug...
            return raw_i
        else:
            return None

    def resolve_type(self):
        # negative indexing is allowed, but redundant here
        elem_types = {self[0].type[i] for i in self._valid_indices if i >= 0}
        if len(elem_types) == 0:
            # _valid_indices is empty
            return None
        elif len(elem_types) == 1:
            ret, = elem_types
            return ret
        elif not self[0].type.is_polymorphic():
            # disjunctive types don't support type variables (see below)
            return types.DisjunctiveType(*list(elem_types))
        else:
            # currently there is not a perfect way for expressions in this else
            # case to be well-typed. Ideally, type variables in disjunctive
            # types would be allowed, but this is quite technically difficult
            # and I don't currently have a use case, so it's on hold. Instead
            # we fall back on an extremely generic type. This works, but it
            # can lead to some potentially surprising effects. Essentially,
            # type adjustment acts on currently valid indices for the index
            # expression, so if there are type variables in multiple disjuncts
            # they all are impacted.
            #
            # Example 1, this case works ~ as you'd expect.
            #     te('L x_n : (a_e, y_Y)[x]').try_adjust_type(tp('<n,n>'))
            # The function itself is type <n,∀X>. (Where ideally, it might be
            # type <n,(e,Y)>, but this is what's currently not supported.)
            # Adjusting this to <n,n> requires that x != 1, and this is
            # supported. The resulting expression has the constraint that
            # x == 1, and the function's type is <n,Y>.
            #
            # Example 2, possibly unexpected behavior.
            #     te("L x_n : t_(X,Y)[x]").try_adjust_type(tp("<n,n>"))
            # There's a potentially desirable behavior here with conditional
            # type variable mappings, where if n is 0, X=e, and if it's 1, Y=e.
            # Currently, type adjustment unconditionally infers that both type
            # variables have to be `n`. That is, the result is the
            # straightforward function: `L x_n : t_(n,n)[x]`. One way to think
            # about this is that the expression `t_(X,Y)[x]` has no index-based
            # subtyping, so `x` can be 0 or 1 at the time of construction, and
            # therefore type inference takes that constraint as primary and
            # adjusts both type variables in consequence.
            #
            # If the type were allowed, this would essentially be the question
            # of how `[X|Y]` unifies with `n`. This code as acting ad hoc as
            # if the answer is [n|n] (which == n) with X=Y=n, where you'd want
            # a weaker type if this were done generally.

            # An alternative would be to just raise an exception here...
            return types.VariableType.any()

    def copy_local(self, arg1, arg2, typ=None, copying=False, **kwargs):
        # because `[]` isn't handled like a normal operator, this can't rely
        # on generic superclass code
        # this is a bit hacky, but we need to reconstruct any inferences on the
        # output type...
        if copying and typ is None:
            typ = self.type
        # XX is passing valid_indices here right
        return self.copy_core(TupleIndex(arg1, arg2, typ=typ, valid_indices=self._valid_indices, **kwargs))

    def __repr__(self):
        # XX some of the complex adjustment cases don't fully repr...
        return "(%s[%s])" % (repr(self.args[0]), repr(self.args[1]))

    def latex_str(self, suppress_parens=False, **kwargs):
        base = f"{self.args[0].latex_str(**kwargs)}[{self.args[1].latex_str(**kwargs)}]"
        if not self[1].meta() and not isinstance(self.type, types.Forall):
            # add a type annotation if the type isn't visible from a concrete
            # index. Showing the Forall also isn't very helpful in practice.
            # XX don't show if tuple is monotyped?
            base += f"_{{{self.type.latex_str(**kwargs)}}}"

        if not suppress_parens:
            base = f"({base})"
        return ensuremath(base)

    def _compile(self):
        if isinstance(self[0], Tuple):
            if (raw_i := self.resolve_index()) is not None:
                # constant case: no need to compile the whole Tuple.
                elem = self.args[0].tuple()[raw_i]._compiled
                return lambda context: elem(context)
            # precompile elements but defer supplying context
            # XX can this be generalized to some non-Tuple self[0]s?
            tup = tuple(a._compiled for a in self[0])
            index = self[1]._compiled
            return lambda context: tup[index(context)](context)
        else:
            # if we don't have a Tuple, it's hard to avoid supplying context
            # immediately. This case also covers when self[0] is a MetaTerm;
            tup = self[0]._compiled
            index = self[1]._compiled
            return lambda context: tup(context)[index(context)]

    def simplify(self, **kwargs):
        if (raw_i := self.resolve_index()) is not None:
            if isinstance(self.args[0], Tuple) or self.args[0].meta():
                # XX why is copy() necessary
                return derived(self.args[0].tuple()[raw_i].copy(),
                    self, "Resolution of index")
            # else fallthrough: non-meta term of a tuple type
        # else fallthrough: non-concrete index
        return self

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        content_type = get_type_system().random_type(max_type_depth, 0.5)
        tup = Tuple.random(ctrl, max_type_depth=max_type_depth,
                                                        allow_empty=False)
        index = random.choice(range(len(tup)))
        return TupleIndex(tup, index)



###############
#
# Binding expressions
#
###############



global recurse_level
recurse_level = 0

# for use in parsing
@dataclass
class BindingOpHeader:
    op_class: type
    var_seq: list[tuple[str, types.TypeConstructor]] # py39 syntax
    restrictor: TypedExpr = None

    def classprop(self, k, default=None):
        return getattr(self.op_class, k, default)

    def ensure_types(self):
        for i in range(len(self.var_seq)):
            if self.var_seq[i][1] is None:
                self.var_seq[i] = (self.var_seq[i][0],
                            default_variable_type(self.var_seq[i][0]))

    def precheck(self):
        # side effect: will initialize any `None` types to the default type
        # for the variable name
        for i in range(len(self.var_seq)):
            if not is_var_symbol(self.var_seq[i][0]):
                raise parsing.ParseError(
                    "Need variable name in binding expression"
                    f" (received `{self.var_seq[i][0]}`)")
            if self.var_seq[i][1] is None:
                self.var_seq[i] = (self.var_seq[i][0],
                            default_variable_type(self.var_seq[i][0]))

        if not self.classprop('allow_multivars') and len(self.var_seq) > 1:
            raise parsing.ParseError(
                f"Operator class `{self.op_class.canonical_name}` does not"
                " allow >1 variables")

        if not self.classprop('allow_novars') and len(self.var_seq) == 0:
            raise parsing.ParseError(
                f"Operator class `{self.op_class.canonical_name}` does not"
                " allow 0 variables")

        if not self.classprop('allow_restrictor') and self.restrictor is not None:
            raise parsing.ParseError(
                f"Operator class `{self.op_class.canonical_name}` does not"
                " allow a restrictor")

        # note: type of restrictor not checked here! Instantiating class is
        # responsible for that.

    def get_kwargs(self, assignment=None):
        kwargs = dict(assignment=assignment)
        if self.classprop('allow_restrictor'):
            kwargs['restrictor'] = tenorm(self.restrictor)
        return kwargs

    def factory(self, body, assignment=None):
        self.precheck()
        if self.classprop('allow_novars') or self.classprop('allow_multivars'):
            # constructor should take an n-ary sequence of variables
            var_arg = [self.var_init(v) for v in self.var_seq]
        else:
            # constructor should take a single variable
            var_arg = self.var_init(self.var_seq[0])

        return self.op_class(var_arg, tenorm(body), **self.get_kwargs())

    @property
    def opname(self):
        return self.op_class.__name__

    def var_init(self, var):
        if isinstance(var, TypedTerm):
            # or just return it?
            varname = var.op
            vartype = var.type
        elif isinstance(var, tuple):
            varname, vartype = var
        else:
            # mainly here to help subclass implementers
            raise NotImplementedError(f"Unknown var for {self.opname}: `{repr(var)}`")

        if not is_var_symbol(varname):
            raise ValueError(f"{self.opname} needs a variable name (got `{repr(varname)}`)")

        return TypedTerm(varname, typ=vartype)

class BindingOp(TypedExpr):
    """Abstract class for a unary operator with a body that binds a single
    variable in its body.

    Never instantiated directly.  To see how to use this, it may be helpful to
    look at the definite description tutorial, which shows how to build an iota
    operator."""

    op_regex = None
    init_op_regex = None

    # set the following in subclasses
    canonical_name = None
    secondary_names = set()
    allow_multivars = False
    allow_novars = False
    op_name_uni = None
    op_name_latex = None

    partiality_weak = True

    # Binding operators mostly have what is commonly called "commutativity" in
    # the logical literature, but is strictly speaking left commutativity only.
    # For some subclasses where this should be False, it is because the relevant
    # expressions simply can't occur (e.g. `SetCondition`, `Iota`). The only
    # really non-commutative subclass is LFun.
    left_commutative = True # y ∀ (x ∀ p) == x ∀ (y ∀ p).
    associative = False # x ∀ (y ∀ p) != (x ∀ y) ∀ p [which is not well-formed]
    left_assoc = False # associativity is (must be) right: (x ∀ (y ∀ (z ∀ p)))

    def __init__(self, var, body, /,
                typ, # require this to be provided, but it may be None (see below)
                *,
                body_type=None,
                assignment=None, copying=False):
        # NOTE: this does not call the superclass constructor

        # default assumption for body type: type of the whole thing = type
        # of the body. This is a bit arbitrary, but is true for standard
        # logical binders.
        if body_type is None:
            body_type = typ

        # Warning: typ may be `None` depending on subclass implementation
        if typ is not None:
            self.type = typ

        self.derivation = None
        self.type_guessed = False
        self.defer = False
        self.let = False
        self.init_args()
        self.init_var_by_instance(var) # XX this does an unnecessary copy
        # TODO: consider overriding __eq__ and __hash__.

        # type constraint: self.var_instance is consistent with variables of
        # the same name within body, and has the corresponding principal type.
        # with copying=True, this constraint (which is fairly heavy) is
        # not ensured.
        if not copying:
            # note! here we intentionally construct an assignment that includes
            # only the bound variable; we don't actually want to *do* variable
            # replacement generally, and type checking for the rest of the
            # assignment should be handled elsewhere.
            sassign = self.scope_assignment()
            try:
                self.init_body(self.ensure_typed_expr(body, body_type,
                                                        assignment=sassign))
            except types.TypeMismatch as e:
                old = e.error
                e.error = f"Failed to ensure body type `{body_type}` for operator class `{self.canonical_name}`"
                if old:
                    e.error += ": " + old
                raise e
            body_env = self.body.get_type_env()
            if self.varname in body_env.terms(): # binding can be vacuous
                body_var_t = body_env.term_type(self.varname, specific=True)
                if body_var_t != self.vartype:
                    # propagate type inference to binding expression
                    new_vartype = body_var_t
                    assert body_var_t is not None
                    self.init_var(self.varname, body_var_t)
            # we call regularize here in case there's any mappings involving
            # the bound variable that need to be finalized
            self.init_body(self.body.regularize_type_env())
            self.init_var_by_instance(
                self.var_instance.under_type_assignment(self.body.get_type_env().type_mapping,
                                                        merge_intersect=False))
            # note for subclasses: if your subclass type is related to the
            # variable type, you should do further updates as needed after
            # this call
        else:
            self.init_body(body)
        self._reduced_cache = [None] * len(self.args)

    def copy(self):
        # on the assumption that type checking in subclasses is generally
        # expensive, don't redo it
        return self.copy_local(*self, copying=True)

    def copy_local(self, *args, **kwargs):
        # this assertion is here because right now, the superclass function
        # signature doesn't match the subclasses, but in a way that will fail
        # silently
        assert type(self) != BindingOp
        return self.copy_core(type(self)(*args, **kwargs))

    def name_of(self, i):
        if i == len(self) - 1:
            return "body"
        else:
            return super().name_of(i)

    def scope_assignment(self, assignment=None):
        assignment = subassignment(assignment)
        if isinstance(self.var_instance, Tuple):
            for v in self.var_instance.tuple():
                assignment[v.op] = v
        else:
            assignment[self.varname] = self.var_instance
        return assignment

    def init_args(self):
        try:
            a = self.args
        except AttributeError:
            self.args = list([None, None])
        assert len(self.args) == 2

    def apply_var_constraints(self):
        # disable let-polymorphic types by default; for most subclasses this
        # is more confusing than useful. Regular polymorphic variables are
        # still allowed, and in fact often extremely useful / necessary for
        # writing abstract combinators, monads, etc.
        # XX this may still be useful for writing combinators, consider relaxing?
        if self.vartype.is_let_polymorphic():
            raise parsing.ParseError(
                f"operator class `{self.canonical_name}` disallows let-polymorphic bound variables (got `{repr(self.var_instance)}`)")

    def init_var(self, name=None, typ=None):
        # XX this has a bunch of flexibility for historical reasons that is now
        # mostly unused. Could still be useful for subclass implementers?
        self.init_args()
        if name is None:
            if typ is None:
                raise ValueError("Missing `init_var` parameters")
            else:
                var_instance = TypedTerm(self.varname, typ)
        else:
            if typ is None:
                var_instance = TypedTerm(name, self.var_instance.type)
            else:
                var_instance = TypedTerm(name, typ)
        self.args[0] = var_instance
        self.op = "%s:" % (self.canonical_name)
        self.apply_var_constraints()

    def init_var_by_instance(self, v):
        self.init_var(v.op, v.type)

    def init_body(self, b):
        self.init_args()
        self.args[1] = b

    @property
    def varname(self):
        if isinstance(self.var_instance, Tuple):
            return None
        return self.var_instance.term_name

    @property
    def vartype(self):
        return self.var_instance.type

    @property
    def var_instance(self):
        return self.args[0]

    @property
    def body(self):
        return self.args[1]        

    def finite_safe(self):
        return (self[0].type.domain.enumerable()
            and self[0].type.domain.finite)

    def type_domain_iter(self):
        # wrap domain elements in MetaTerms
        from .meta import MetaTerm
        yield from map(
            lambda x: MetaTerm(x, typ=self[0].type),
            iter(self[0].type.domain))

    def domain_iter(self):
        # this may be (probably is!) a non-stopping iterator
        return self.type_domain_iter()

    def domain_cardinality(self):
        if isinstance(self.vartype.domain, types.PolymorphicDomainSet):
            # refuse to try to give an answer. In principle, we could probably
            # get away with returning `inf`. But this is analytically wrong:
            # there can be atomic types that (under domain restriction or
            # otherwise) have cardinality 1, and a type variable could resolve
            # to this. So None here means that it is simply tbd until the
            # polymorphism is resolved.
            return None
        return self.vartype.domain.cardinality()

    @classmethod
    def compile_ops_re(cls):
        """Recompile the regex for detecting operators."""
        global registry
        op_names = (registry.binding_ops.keys()
                                | registry.canonicalize_binding_ops.keys())
        # sort with longer strings first, to avoid matching subsets of long
        # names i.e. | is not greedy, need to work around that.
        op_names = list(op_names)
        op_names.sort(reverse=True)
        # somewhat ad hoc: allow `λx`. (Could add unicode quantifiers?)
        # TODO: would it be better to always require a space?
        nospace = {"λ"}

        nospace_ops = [o for o in op_names if o in nospace]
        if len(op_names) == 0:
            BindingOp.op_regex = None
            BindingOp.init_op_regex = None
        else:
            regex = f"({'|'.join(op_names)})\\s+"
            if nospace_ops:
                regex = f"(?:({'|'.join(nospace_ops)})|{regex})"
            BindingOp.op_regex = re.compile(regex)
            BindingOp.init_op_regex = re.compile(r'^\s*' + regex)

    @classmethod
    def init_op_match(cls, s):
        if BindingOp.init_op_match and BindingOp.init_op_regex is not None:
            # TODO: is there a clever way to do this with a single match group
            match = re.match(BindingOp.init_op_regex, s)
            if match:
                if match.group(2):
                    return match.group(2), match.end(2)
                else:
                    return match.group(1), match.end(1)
        return None

    def alpha_convert(self, *new_varname):
        """Produce an alphabetic variant of the expression w.r.t. the bound
        variable(s), with `new_varname` as the new name(s).

        Returns a copy.  Will not affect types of either the expression or the
        variables."""
        if len(new_varname) == 0:
            return self

        if isinstance(self.var_instance, Tuple):
            vseq = [v.op for v in self.var_instance.tuple()]
        else:
            vseq = (self.varname,)

        if len(new_varname) > len(vseq):
            raise ValueError(f"Too many arguments supplied to `alpha_convert` (got {len(new_varname)}) for `{repr(self)}`")

        remap = {vseq[i]: new_varname[i] for i in range(len(new_varname))}

        # this is written in a fairly general way so as to not make assumptions
        # about other args that subclasses may introduce. In particular, copy
        # `restrictor` if it is present on RestrictedBindinOp sublcasses. If
        # subclasses would need to change anything but the var and the body,
        # they'll need to not rely on this code.
        args = self.args.copy()
        if isinstance(self.var_instance, Tuple):
            args[0] = variable_convert(args[0], remap)
        else:
            args[0] = TypedTerm(new_varname[0], self.vartype)

        if not self.vacuous():
            args[1] = variable_convert(args[1], remap)
        # restrictor, if any, is not in the scope of the binder, leave unchanged
        return self.copy_local(*args)

    def latex_op_str(self):
        return self.latex_op_str_short()

    def latex_op_str_short(self):
        return "%s %s_{%s} \\: . \\:" % (self.op_name_latex, 
                                                self.varname, 
                                                self.vartype.latex_str())

    def latex_str(self, assignment=None, suppress_parens=False, **kwargs):
        assignment = self.scope_assignment(assignment=assignment)
        suppress_sub = True
        if isinstance(self.body, Tuple):
            suppress_sub = False
        body = self.body.latex_str(assignment=assignment,
                                    suppress_parens=suppress_sub, **kwargs)
        base = f"{self.latex_op_str()} {body}"
        if not suppress_parens:
            base = f"({base})"
        return ensuremath(base)

    def __repr__(self):
        return "(%s %s: %s)" % (self.op_name, repr(self.var_instance),
                                                            repr(self.body))

    @property
    def op_name(self):
        if (self.op_name_uni is not None
                            and self.op_name_uni in self.secondary_names):
            return self.op_name_uni
        else:
            return self.canonical_name


    def free_terms(self, var_only=False):
        return super().free_terms(var_only=var_only) - {self.varname}

    def bound_variables(self):
        return super().bound_variables() | {self.varname}

    def calc_type_env(self, recalculate=False):
        # general code used in almost all BindingOp subclasses.

        # start with the type environment from the body
        sub_env = self.body.get_type_env(force_recalc=recalculate).copy()
        # ensure any variable types introduced by the variable show up even if
        # the variable does not appear in the subformula
        sub_env.add_type_to_var_set(self.var_instance.type)
        # the variable does not locally appear, because it is not free in this
        # expression -- so if it is there (probably) we remove the term itself.
        # its impact on type inference remains.
        if self.varname in sub_env.terms():
            sub_env.remove_term(self.varname)
        return sub_env

    def vacuous(self):
        """Return true just in case the operator's variable is not free in the
        body expression."""
        fv = self[1].free_variables()
        if isinstance(self.var_instance, Tuple):
            return any(v in fv for v in self.var_instance)
        else:
            return self.varname not in fv

    def term(self):
        return False

    def project_partiality_strict(b, body, condition):
        # refactor somehow?
        from .sets import ConditionSet
        from .quantifiers import Forall
        b_cls = type(b)
        if isinstance(b, ConditionSet) or isinstance(b, LFun):
            return b
        else: # IotaPartial handled in subclass
            return Partial(b_cls(b.var_instance, body),
                                            Forall(b.var_instance, body))

    def project_partiality_weak(b, body, condition):
        # refactor somehow?
        from .sets import ConditionSet
        from .quantifiers import Forall, Exists, Iota, ExistsExact
        b_cls = type(b)
        if isinstance(b, Forall):
            return Partial(b_cls(b.var_instance, body),
                                            b_cls(b.var_instance, condition))
        elif isinstance(b, Exists) or isinstance(b, ExistsExact):
            return Partial(b_cls(b.var_instance, body & condition),
                                            b_cls(b.var_instance, condition))
        elif isinstance(b, Iota): # does this lead to scope issues for the condition?
            return Partial(b_cls(b.var_instance, body & condition),
                                        Exists(b.var_instance, condition))
        elif isinstance(b, ConditionSet) or isinstance(b, LFun):
            return b
        else: # IotaPartial handled in subclass
            # is this really a type issue?
            raise TypeMismatch(b, None,
                    error="No implemented way of projecting partiality for BindingOp %s"
                    % repr(type(b).__name__))

    def calculate_partiality(self, vars=None, **sopts):
        if vars is None:
            vars = set()
        if isinstance(self, LFun):
            vars |= {self.varname}

        # defer any further calculation if there are bound variables in the body
        if vars & self.body.free_variables():
            return self
        result = self

        new_body = result.body.calculate_partiality(vars=vars, **sopts)
        if new_body is not result.body:
            result = derived(result.subst(1, new_body),
                            result,
                            f"Partiality calculation (recursion on {self.name_of(1)})",
                            subexpression=new_body)
        if isinstance(result[1], Partial):
            if result[1].condition == True:
                return derived(self.copy_local(self.var_instance, result[1]),
                        result,
                        "Partiality calculation (trivial body condition)")

            if self.varname in result[1].condition.free_variables():
                if BindingOp.partiality_weak:
                    return derived(
                        result.project_partiality_weak(result[1].body,
                                                     result[1].condition),
                        result,
                        "Partiality (weak projection)")
                else:
                    return derived(
                        result.project_partiality_strict(result[1].body,
                                                       result[1].condition),
                        result,
                        "Partiality (strict projection)")
            else:
                new_condition = result[1].condition
                new_self = self.copy_local(self.var_instance, result[1].body)
                return derived(Partial(new_self, new_condition),
                    result,
                    "Partiality (unquantified condition)")
        else:
            return result

    @classmethod
    def try_parse_header(cls, struc, assignment=None, locals=None):
        """Try and parse the header of a binding operator expression, i.e.
        everything up to the body including ':'.

        If this succeeds, it will return a tuple with the class object, the
        variable name, the variable type, and the string after the ':'' if any.

        If it fails, it will either return None or raise an exception.  That
        exception is typically a ParseError.
        """

        global registry

        if len(struc) == 0 or not isinstance(struc[0], str):
            return None

        potential_header = struc[0]
        i = 0
        if not (op_match := cls.init_op_match(potential_header)):
            raise parsing.ParseError(
                "Unknown operator when trying to parse binding expression",
                potential_header, None, met_preconditions=False)
        op_name, i = op_match

        if op_name in registry.canonicalize_binding_ops:
            op_name = registry.canonicalize_binding_ops[op_name]
        if op_name not in registry.binding_ops:
            raise Exception(
                "Can't find binding operator '%s'; should be impossible"
                % op_name)
        op_class = registry.binding_ops[op_name]

        i = parsing.consume_whitespace(potential_header, i)

        new_struc = [potential_header[i:]] + struc[1:]
        # if `:` can ever appear in types, this will go wrong
        main_split = parsing.struc_split(new_struc, ":")
        # XX the whitespace here is a bit unfortunate. Currently, it prevents
        # matching in a complex functional type...
        restric_split = parsing.struc_split(main_split[0], " <<")
        # assumption: no structure in header before <<
        if len(restric_split) > 1 and len(restric_split[0]) > 1:
            raise parsing.ParseError(
                "Extraneous material in binding expression before `<<`",
                s=flatten_paren_struc(main_split[0]),
                met_preconditions=True)

        try:
            var_seq = try_parse_term_sequence(restric_split[0], lower_bound=None,
                                    upper_bound=None, assignment=assignment)
        except parsing.ParseError as e:
            # somewhat involved logic: try to parse the var sequence before
            # reporting errors about a missing `:`. However, if we are missing
            # a `:`, mark `met_preconditions` as false so that the parser isn't
            # committed to a binding op header.
            if len(main_split) != 2:
                e.met_preconditions = False
            raise e
        if (len(main_split) != 2):
            # possibly should change to met_preconditions = True in the future.
            # At this point, we have seen a binding expression token.
            raise parsing.ParseError(
                "Missing ':' in binding expression",
                potential_header,
                met_preconditions=True)
        restric = None
        if len(restric_split) > 1:
            # ok, the right side of the split should now be parseable as a
            # set expression
            with parsing.parse_error_wrap(
                        "Binding expression has unparsable restrictor",
                        paren_struc=restric_split[1]):
                # XX named variables should not occur free here
                restric = TypedExpr.try_parse_paren_struc_r(restric_split[1],
                        assignment=assignment, locals=locals)

        return (BindingOpHeader(op_class=op_class, var_seq=var_seq, restrictor=restric),
                main_split[1])

    @classmethod
    def try_parse_binding_struc_r(cls, struc, assignment=None, locals=None,
                                                                vprefix="ilnb"):
        """Attempt to parse structure `s` as a binding structure.  Used by the
        factory function.
        
        assignment: a variable assignment to use when parsing.

        `struc` is a semi-AST with all parenthetical structures parsed.
        (See `parsing.parse_paren_str`.)

        Format: 'Op v : b'
          * 'Op' is one of 'lambda', 'L', 'λ', 'Forall', 'Exists', 'Iota'.
            (Subclasses can register themselves to be parsed.)
          * 'v' is a variable name expression (see try_parse_typed_term),
             e.g. 'x_e'
          * 'b' is a function body, i.e. something parseable into a TypedExpr.

        If 'v' does not provide a type, it will attempt to guess one based on
        the variable name. The body will be parsed using a call to the
        recursive `TypedExpr.try_parse_paren_struc_r`, with a shifted assignment
        using the new variable 'v'.

        Returns a subclass of BindingOp.
        """

        struc_arg = struc
        # TODO: integrate with general bracket handling
        if (left := parsing.bracketed(struc)):
            struc = parsing.debracket(struc)
        if (result := BindingOp.try_parse_header(struc,
                            assignment=assignment, locals=locals)) is None:
            return None
        header, struc = result

        assignment = subassignment(assignment)
        for var_tuple in header.var_seq:
            (v,t) = var_tuple
            assignment[v] = TypedTerm(v, t)
        body = None
        with parsing.parse_error_wrap(
                        "Binding expression has unparsable body",
                        paren_struc=struc_arg):
            body = TypedExpr.try_parse_paren_struc_r(struc,
                        assignment=assignment, locals=locals, vprefix=vprefix)

        if body is None:
            raise parsing.ParseError(
                "Can't create body-less binding expression",
                parsing.flatten_paren_struc(struc_arg), None)

        with parsing.parse_error_wrap("Binding expression parse error",
                                    paren_struc=struc_arg):
            result = header.factory(body, assignment=assignment)
        # TODO: integrate with general set handling
        if left == "{":
            from .sets import ListedSet
            result = ListedSet(result)
        return result

    @classmethod
    def join(cls, args, empty=None):
        # `empty` is ignored
        if len(args) == 0:
            raise ValueError(f"Need at least 1 argument for BindingOp.join (got `{repr(args)}`)")
        if len(args) == 1:
            return args[0]

        cur = args[-1]
        for i in range(len(args) - 1, 0, -1):
            # this will error on non-variables in everything but args[-1]
            cur = cls(args[i - 1], cur)

        return cur

    @classmethod
    def random(cls, ctrl, body_type=types.type_t, max_type_depth=1):
        from . import test
        var_type = get_type_system().random_type(max_type_depth, 0.5, allow_variables=False)
        variable = test.random_term(var_type, usedset=test.random_used_vars,
                                                prob_used=0.2, prob_var=1.0)
        test.random_used_vars |= {variable}
        return cls(variable, ctrl(typ=types.type_t))


class LFun(BindingOp):
    """A typed function.  Can itself be used as an operator in a TypedExpr.

    """
    canonical_name = "Lambda"
    secondary_names = {"L", "λ", "lambda"}
    op_name_uni="λ"
    op_name_latex="\\lambda{}"
    commutative = False
    left_commutative = False
    collectable = False

    def __init__(self, var, body, *, let=False, typ=None, **kwargs):
        # type constraint: typ == <var.type, body.type>
        # unify_fun handles None parameters gracefully
        principal = get_type_system().unify_fun(typ, var.type, body.type)
        if principal is None:
            # this is a bug if unify_fun fails to combine arbitrary arg/ret
            # pairs in absence of a target type
            assert typ is not None
            raise TypeMismatch(var, body,
                error=f"Type inference on Lambda expression failed: target type {repr(typ)}")
        # we should now have a principal type that both var and body can meet exactly
        var = self.type_constraint(var, principal.left, constant=True)
        body = self.type_constraint(body, principal.right, constant=True)

        super().__init__(var, body, typ=principal, body_type=body.type,
            **kwargs)
        # superclass may trigger further type inference when reconciling the
        # bound variable with the body, so set the type here. No further
        # changes required to self.
        self.type = FunType(self.vartype, body.type)
        self.let = let

    def apply_var_constraints(self):
        pass

    @property
    def argtype(self):
        return self.type.left

    @property
    def returntype(self):
        return self.type.right

    def functional(self):
        return True # no need to do any calculations

    def will_reduce(self, arg):
        return True

    def _compile(self):
        body = self[1]._compiled
        if is_te(self[0], LFun) and self[0].vacuous():
            # don't try to evaluate the argument at all in this case, since it
            # will be discarded. *caveat*: this may prevent constraints from
            # being applied, e.g. from Partial? Note that the argument will
            # still be *compiled* if it's part of an ApplicationExpr.
            return lambda context: lambda x: self[0]._compiled(context)
        qualname = self._compiled_repr()
        def outer(context):
            # unfortunate, but something is needed to protect other users of
            # `context` from side effects, given the way deferred application
            # is handled
            context = dict(context)
            def inner(x):
                # assumption: x is compiled and normalized. In principle this
                # could normalize; currently wrapper functions handle this
                context[self.varname] = x
                return body(context)
            inner.__qualname__ = qualname
            return inner
        return outer

    def apply(self,arg):
        """Apply an argument directly to the function.

        `__call__` plus `reduce` is (almost) equivalent to `apply`, but using
        `apply` directly will not generate a derivation."""

        # do I really want flexible equality here??
        # TODO: return to this.  Right now a type mismatch still gets raised
        # during beta reduction.
        ts = get_type_system()
        if ts.eq_check(self.argtype, arg.type):
            result = alpha_convert(self, unsafe_variables(self, arg))
            result = beta_reduce_ts(result.body, result.varname, arg)
            return result
        else:
            raise TypeMismatch(self, arg, error="Function-argument application: mismatched argument type")

    def compose(self, other):
        """Function composition."""
        from lamb.combinators import fun_compose
        # this implementation requires polymorphism
        return fun_compose(self, other)

    def __mul__(self, other):
        """Override `*` as function composition for LFuns.  Note that this
        _only_ works for LFuns currently, not functional constants/variables."""
        # XX generalize or remove magic function
        return self.compose(other)

    @classmethod
    def random(self, ctrl):
        from . import test
        # not great at reusing bound variables
        ftyp = get_type_system().random_from_class(types.FunType)
        return test.random_lfun(ftyp, ctrl)


class ChainFun(SyncatOpExpr):
    """This class chains two functions together to produce a new function. When
    the new function is called, it first tries the second, and if a DomainError
    is thrown, tries the first. (As the name indicates, this is roughly modeled
    after collections.ChainMap.)
    """
    canonical_name = "+"
    commutative = False
    associative = True

    # argument signature set in __init__.py
    # arg_signature = tp("(<X,Y>,<X,Y>)")

    def __init__(self, f1, f2, *, typ=None, **kwargs):
        f1 = self.type_constraint(f1, types.FunType)
        f1, f2 = self.type_constraint(f1, f2)
        typ, _ = self.type_constraint(f1.type, typ)
        super().__init__(typ, f1, f2, tcheck_args=False)

    def functional(self):
        return True # no need to do any calculations

    def will_reduce(self, arg):
        # XX this might diverge from some cases of simplify + reduce?
        return self[0].will_reduce(arg) and self[1].will_reduce(arg)

    def _compile(self):
        from .meta import DomainError, MetaTerm
        f1 = self[0]._compiled
        f2 = self[1]._compiled
        def outer(context):
            f1_c = f1(context)
            f2_c = f2(context)
            def inner(x):
                try:
                    return MetaTerm._apply_impl(f2_c, x)
                except DomainError:
                    # XX if this fails, the error only mentions the final
                    # function
                    return MetaTerm._apply_impl(f1_c, x)
            return inner
        return outer

    def apply(self, arg):
        from .meta import DomainError
        try:
            return self[1].apply(arg)
        except DomainError:
            return self[0].apply(arg)

    def _try_merge_funs(self):
        f1 = self[0] # for readability
        f2 = self[1]
        if f1.meta() and f2.meta():
            # for this case, we can use MetaTerm code that will return a
            # MetaTerm
            return f1.try_merge(f2)

        # # XX meta implementation details shouldn't be here
        if f2.meta() and isinstance(f2.op, collections.abc.Set):
            return f2

        # otherwise, if f1 and f2 are both implemented via maps, find the maps
        # and use dict updating to combine them
        if f1.meta():
            # XX a set implementation MetaTerm fun is in principle handleable
            # here
            try:
                lmap = f1.dict()
            except ValueError:
                return None
        elif isinstance(f1, MapFun):
            lmap = f1.arg_map
        else:
            # not a mergeable function class
            return None

        if f2.meta():
            try:
                rmap = f2.dict()
            except ValueError:
                return None
        elif isinstance(f2, MapFun):
            rmap = f2.arg_map
        else:
            # not a mergeable function class
            return None
        # merge the maps in order. We do this in a somewhat complicated way so
        # that keys in both are ordered after keys in lmap; if we used the full
        # lmap, keys in both would inherit their ordering from lmap.
        result = {k: lmap[k] for k in lmap if k not in rmap}
        result.update(rmap)
        return MapFun(*[(k, result[k]) for k in result], typ=self.type, copying=True)

    def simplify(self, **kwargs):
        merged = self._try_merge_funs()
        if merged is not None:
            return derived(merged, self, "Map chaining")
        return self

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        # XX this probably doesn't generate very reasonable examples
        ftyp = get_type_system().random_from_class(types.FunType)
        f1 = random_ctrl_fun(typ=ftyp)
        f2 = random_ctrl_fun(typ=ftyp)
        return ChainFun(f1, f2)


class MapFun(TypedExpr):
    canonical_name = "Fun"
    op_name_uni="Fun"
    op_name_latex="Fun"
    pre_simplify = True

    def __init__(self, *args, typ=None, copying=False, **kwargs):
        if copying and typ is None:
            raise ValueError("Bug: MapFun copying requires `typ` to be specified")
        if not copying:
            # *args is a sequence of tuples. Note that this does not check TupleType,
            # but requires a Tuple.
            for a in args:
                # XX MetaTerm tuple?
                if (is_te(a) and not isinstance(a, Tuple)
                                or not is_te(a) and not isinstance(a, collections.abc.Sequence)
                                or len(a) != 2):
                    raise TypeError(f"MapFun requires a sequences of pairs (received non-pair `{repr(a)}`)")

            # normalize into python lists so we can work in place
            args = [[a[0], a[1]] for a in args]

            if typ is not None and isinstance(typ, FunType):
                # start with `typ` so we don't have to do it later
                ltype = typ[0]
                rtype = typ[1]
            elif len(args):
                ltype = args[0][0].type
                rtype = args[0][1].type # start with first pair
            else:
                # could be anything
                ltype = types.VariableType.any()
                rtype = types.VariableType.any()

            # type inference here is somewhat horrendous
            def _update_types(ityp, args, i):
                # take a single pass through range elements and apply `ityp` as a
                # constraint
                for j in range(len(args)):
                    ityp, args[j][i] = self.type_constraint(ityp, args[j][i],
                        error=f"MapFun elements must have compatible types (`{repr(args[j][i])}` at type `{ityp}`)")
                return ityp

            new_ltype = _update_types(ltype, args, 0)
            new_rtype = _update_types(rtype, args, 1)
            if typ is not None and not isinstance(typ, FunType):
                # not handled above, so we still need to reconcile with typ...
                typ, _ = self.type_constraint(types.FunType(new_ltype, new_rtype), typ)
                # if this last step led to further changes, do the resulting type
                # coercion
                if typ[0] != new_ltype:
                    typ = types.FunType(_update_types(typ[0], args, 0), typ[1])
                if typ[1] != new_rtype:
                    typ = types.FunType(typ[0], _update_types(typ[1], args, 1))
            else:
                typ = types.FunType(new_ltype, new_rtype)

        args = [Tuple(*a) for a in args]

        super().__init__("MapFun", *args)
        self.type = typ
        self.map_simplified = len(self.args) <= 1
        self.left_concrete = all(is_concrete(a[0]) for a in self.args)
        self.arg_map = utils.frozendict(self.args)

    def _eq_elem(self):
        return (self.arg_map, self.map_simplified)

    def _compile(self):
        from .meta import OutOfDomain
        # assumption: keys are purely meta
        keys = {k: k._compiled for k in self.arg_map}
        m = {k: self.arg_map[k]._compiled for k in self.arg_map}
        def outer(context):
            # we can't construct the final map until this point. This could be
            # a bit optimized for meta-only maps, since those keys would be
            # safe to used directly
            full_map = {keys[k](context): m[k] for k in keys}
            def inner(x):
                # XX deferred context issues here
                if not x in full_map:
                    # use of self._compiled here is safe, because this function
                    # can't be called before the current compilation returns
                    raise OutOfDomain(self._compiled, x)
                return full_map[x](context)
            return inner
        return outer

    def will_reduce(self, arg):
        return self.left_concrete and is_concrete(arg)

    def apply(self, arg):
        # this will go more badly wrong than usual if will_reduce is not
        # checked!
        from .meta import OutOfDomain
        if get_type_system().eq_check(self.type[0], arg.type):
            if not arg in self.arg_map:
                raise OutOfDomain(self, arg)
            return self.arg_map[arg]
        else:
            raise TypeMismatch(self, arg,
                error="Function-argument application: mismatched argument type")

    def copy_local(self, *args, typ=None, copying=False, **kwargs):
        if (copying or len(args) == 0) and typ is None:
            # empty maps: don't allow any types weaker than self.type
            # to be inferred
            typ = self.type

        return self.copy_core(MapFun(*args, typ=typ, **kwargs))

    def do_simplify(self, **sopts):
        if self.map_simplified:
            return self

        args = [(k, self.arg_map[k]) for k in self.arg_map]
        result = self.copy_local(*args, copying=True)
        result.map_simplified = True
        result.arg_map = self.arg_map # preserve cosmetic order
        # don't set a derivation
        return result

    def simplify(self, **sopts):
        result = self.do_simplify(**sopts)
        if result is not self:
            result = derived(result, self, desc="Map normalization")
        return result

    def __repr__(self):
        if len(self) == 0:
            # `{}` means empty set, not empty function
            return 'Fun()'
        if self.map_simplified:
            # show cosmetic order from arg_map
            body = ", ".join([f"{repr(p)}:{repr(self.arg_map[p])}" for p in self.arg_map])
        else:
            body = ", ".join([f"{repr(p[0])}:{repr(p[1])}" for p in self.args])
        return f"{{{body}}}"

    def latex_str(self, **kwargs):
        # XX use vertical layout?
        if self.map_simplified:
            # show cosmetic order from arg_map
            args = [(k, self.arg_map[k]) for k in self.arg_map]
        else:
            args = self.args
        inner = ", ".join(
            [f"{p[0].latex_str(**kwargs)}\\rightarrow{{}}{p[1].latex_str(**kwargs)}"
                    for p in args])
        if not len(self.args):
            # show an explicit type for the empty map
            return utils.ensuremath(f"\\{{{inner}\\}}_{{{self.type.latex_str()}}}")
        else:
            return utils.ensuremath(f"\\left\\{{{inner}\\right\\}}")

    @classmethod
    def from_dict(cls, d):
        return cls(*[(k, d[k]) for k in d])


TypedExpr.add_local("Fun", MapFun)


def reset():
    global registry, _namespace
    reset_type_system()
    _namespace = Namespace()


registry = OperatorRegistry()
reset()
