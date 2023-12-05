import sys, re, logging, random, functools, inspect
import collections
from numbers import Number

import lamb
from lamb import types, parsing, utils
from lamb.utils import ensuremath
from lamb.types import TypeMismatch, type_e, type_t, type_n
from lamb.types import type_property, type_transitive, BasicType, FunType
# meta.ply is the only meta module imported by core
from .ply import derived, collectable, multisimplify, alphanorm, get_sopt
from .ply import simplify_all
from .ply import is_var_symbol, unsafe_variables, alpha_convert, beta_reduce_ts
from .ply import term_replace_unify, variable_convert, alpha_variant
from .ply import commutative, associative, left_commutative, right_commutative

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


global _constants_use_custom, _type_system
_constants_use_custom = False


def constants_use_custom(v):
    """Set whether constants use custom display routines."""
    global _constants_use_custom
    _constants_use_custom = v

_type_system = types.poly_system

# TODO: could consider associating TypedExpr with a type system rather than
# using the global variable. advantages: generality.  Disadvantages: may be a
# little pointless in practice?
def set_type_system(ts):
    """Sets the current type system for the metalanguage.  This is a global
    setting."""
    global _type_system
    _type_system = ts

def get_type_system():
    """Gets the current (global) type system for the metalanguage."""
    return _type_system

def ts_unify(a, b):
    """Calls the current type system's `unify` function on types `a` and `b`.
    This returns a unified type, or `None` if the two can't be unified."""
    return get_type_system().unify(a, b)


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


def te(s, let=True, assignment=None):
    """Convenience wrapper for `lang.TypedExpr.factory`."""
    result = TypedExpr.factory(s, assignment=assignment)
    if let and isinstance(result, TypedExpr):
        result = let_wrapper(result)
    return result


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


def typed_expr(s):
    # class method replaces this.  Call this instead of factory, which has a 
    # slightly different semantics -- factory will make a copy if handed a
    # TypedExpr.
    return TypedExpr.ensure_typed_expr(s)

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
    return type_e

def default_type(s):
    if isinstance(s, TypedExpr):
        return s.type
    elif isinstance(s, bool):
        return type_t
    elif types.is_numeric(s):
        return type_n
    elif isinstance(s, str):
        t = utils.num_or_str(s)
        if types.is_numeric(s):
            return type_n
        elif isinstance(s, bool):
            return type_t
        elif is_var_symbol(t):
            return default_variable_type(s)
        else:
            #TODO, better default
            return type_t
    else:
        # TODO: more default special cases?  predicates?
        raise NotImplementedError


def let_compact_type_vars(*args, unsafe=None, store_mapping=False):
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
    envs = [a.get_type_env() for a in args]
    tenv = set().union(*[e.used_vars() for e in envs])

    compacted_map = types.compact_type_set(tenv, unsafe=unsafe)
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



class OperatorRegistry(object):
    class OpDesc(object):
        def __init__(self, _cls, *targs):
            self.name = _cls.canonical_name
            self.cls = _cls
            self.arity = len(targs)
            # XX this should eventually just use the full type system
            self.targs = targs

        def __hash__(self):
            # will prevent multiple overloads at the same arity using the
            # same class...
            return hash(self.name) ^ hash(self.cls.__name__) ^ hash(self.arity)

        def __eq__(self, other):
            return (self.name == other.name
                and self.cls.__name__ == other.cls.__name__
                and self.arity == other.arity
                and self.targs == other.targs)

        def __str__(self):
            return f"OpDesc({self.name}, {self.cls.__name__}, {self.arity})"

        def __repr__(self):
            # n.b. not a true repr
            return str(self)

        def get_names(self):
            # maybe include unicode?
            return [self.name] + list(self.cls.secondary_names)

        def has_blank_types(self):
            for t in self.targs:
                if t is None:
                    return True
            return False

        def check_types_viable(self, *types, strict_none=False):
            # None generally means don't check this arg place; a custom
            # check_viable function for the class usually does the work.
            # If the relevant types are not in the current type system, this
            # will fail.
            if self.arity != len(types):
                return False

            for i in range(len(types)):
                # in `strict_none` mode, supply None for an argument slot to
                # match None, otherwise, mismatch
                if (strict_none and self.targs[i] is None or types[i] is None
                            and self.targs[i] != types[i]):
                    return False

                # otherwise, None in either the op or input slot skips
                if types[i] is None or self.targs[i] is None:
                    continue

                if not ts_compatible(self.targs[i], types[i]):
                    return False
            return True

        def check_viable(self, *args):
            # if the class has a custom check_viable, defer entirely to that
            if callable(getattr(self.cls, "check_viable", None)):
                return self.cls.check_viable(*args)

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

    def add_operator(self, _cls, *targs):
        desc = self.OpDesc(_cls, *targs)
        for name in desc.get_names():
            # use dicts and not sets for the ordering
            if not name in self.ops:
                self.ops[name] = dict()
            self.ops[name][desc] = True
        if not desc.arity in self.arities:
            self.arities[desc.arity] = dict()
        self.arities[desc.arity][desc] = True

    def get_descs(self, op, *types):
        all_matches = list(self.ops[op].keys())
        if len(types): # can't handle 0-ary operators if such a thing ever exists
            return [o for o in all_matches if o.check_types_viable(*types, strict_none=True)]
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

    def expr_factory(self, op, *args):
        """Given some operator/relation symbol with arguments, construct an
        appropriate TypedExpr subclass for that operator."""

        if not op in self.ops:
            raise parsing.ParseError("Unknown operator symbol `%s`" % op)

        matches = [o for o in self.ops[op].keys() if o.arity == len(args)]
        if not len(matches):
            raise parsing.ParseError("No %d-ary operator symbol `%s`" % (len(args), op))

        matches = [o for o in matches if o.check_viable(*args)]

        # Prioritize generic operators over specific operators. Generic
        # operators should explicitly make exceptions for specific operators
        # as needed. TODO: this is extremely ad hoc
        if len(matches) > 1:
            matches = [o for o in matches if o.has_blank_types()]

        if not len(matches):
            raise parsing.ParseError(
                "No viable %d-ary operator symbol `%s` for args `%s`"
                    % (len(args), op, repr(args)))

        # this shouldn't come up for the built-in libraries, but should this
        # be made more informative for user cases?
        if len(matches) > 1:
            raise parsing.ParseError(
                "Ambiguous %d-ary operator symbol `%s` for args `%s`"
                    % (len(args), op, repr(args)))

        return self.apply_custom_transforms(matches[0].cls, matches[0].cls(*args))

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


global registry
registry = OperatorRegistry()

def op_expr_factory(op, *args):
    global registry
    return registry.expr_factory(op, *args)


############### Type unification-related code

class TypeEnv(object):
    def __init__(self, var_mapping=None, type_mapping=None):
        self.type_var_set = set()
        if type_mapping is None:
            self.type_mapping = dict()
        else:
            self.type_mapping = type_mapping
        if var_mapping is None:
            self.var_mapping = dict()
        else:
            self.var_mapping = var_mapping
        self.update_var_set()

    def _repr_html_(self):
        s = "<table>"
        s += ("<tr><td>Term mappings:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.dict_latex_repr(self.var_mapping))
        s += ("<tr><td>Type mappings:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.dict_latex_repr(self.type_mapping))
        s += ("<tr><td>Type variables:&nbsp;&nbsp; </td><td>%s</td></tr>" %
                                    utils.set_latex_repr(self.type_var_set))
        s += "</table>"
        return s

    def update_var_set(self):
        s = types.vars_in_env(self.var_mapping)
        s = s | set(self.type_mapping.keys())
        for m in self.type_mapping:
            s  = s | self.type_mapping[m].bound_type_vars()
        self.type_var_set = s

    def used_vars(self):
        # requires up-to-date var set...
        return self.type_var_set - set(self.type_mapping.keys())

    def term_by_name(self, vname):
        if vname in self.var_mapping:
            return TypedTerm(vname, self.var_mapping[vname],
                                                        defer_type_env=True)
        else:
            return None

    def add_var_mapping(self, vname, typ):
        result = self.try_add_var_mapping(vname, typ)
        if result is None:
            raise TypeMismatch(self.term_by_name(vname), typ,
                error=f"instances of term `{vname}` have distinct types")
        return result

    def try_add_var_mapping(self, vname, typ):
        if vname in self.var_mapping:
            principal = self.try_unify(self.var_mapping[vname], typ,
                                                        update_mapping=True)
            if principal is None:
                return None
            
            assert principal is not None
            self.var_mapping[vname] = principal
            self.update_type_vars()
        else:
            assert typ is not None
            self.var_mapping[vname] = typ
            principal = typ
        self.add_type_to_var_set(principal)
        return principal

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

    def update_type_vars(self):
        for k in self.var_mapping:
            # note that the following is not generally safe, but here we are
            # working with TypedTerms that have no TypeEnv
            new_type = self.var_mapping[k].sub_type_vars(self.type_mapping)
            self.var_mapping[k] = new_type

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
            self.update_type_vars()
        return principal

    def add_type_mapping(self, type_var, typ, defer=False):
        principal = self.try_add_type_mapping(type_var, typ, defer=defer)
        if principal is None:
            raise TypeMismatch(self.type_mapping[type_var], typ,
                error="Failed to unify type variable %s across contexts" % type_var)
        return principal
          

    def merge(self, tenv):
        for v in tenv.type_mapping:
            self.add_type_mapping(v, tenv.type_mapping[v], defer=True)
        self.update_type_vars()
        for v in tenv.var_mapping:
            self.add_var_mapping(v, tenv.var_mapping[v])
        self.type_var_set |= tenv.type_var_set
        return self

    def intersect_merge(self, tenv):
        for v in tenv.type_mapping:
            if (v in self.type_var_set
                    or len(tenv.type_mapping[v].bound_type_vars()
                                                & self.type_var_set) > 0):
                self.add_type_mapping(v, tenv.type_mapping[v], defer=True)
        self.update_type_vars()
        for v in tenv.var_mapping:
            self.add_var_mapping(v, tenv.var_mapping[v])
        return self

    def copy(self):
        env = TypeEnv(self.var_mapping.copy(), self.type_mapping.copy())
        env.type_var_set = self.type_var_set.copy()
        return env

    def __repr__(self):
        return ("[TypeEnv: Variables: "
            + repr(self.var_mapping)
            + ", Type mapping: "
            +  repr(self.type_mapping)
            + ", Type variables: "
            + repr(self.type_var_set)
            + "]")

def merge_type_envs(env1, env2, target=None):
    """Merge two type environments.  A type environment is simply an assignment,
    where the mappings to terms are used to define types. Other mappings are
    ignored.

    If `target` is set, it specifies a set of variable names to specifically
    target; anything not in it is ignored.

    If `target` is None, all mappings are merged."""
    ts = get_type_system()
    result = dict()
    for k1 in env1:
        if target and not k1 in target:
            continue
        if (not env1[k1].term()):
            continue
        if k1 in env2:
            unify = ts_unify_with(env1[k1], env2[k1],
                error="Failed to unify types across distinct instances of term")
            # if the previous call succeeds, it should be impossible to get
            # an adjustment failure here...
            result[k1] = env1[k1].try_adjust_type(unify)
        else:
            result[k1] = env1[k1]
    for k2 in env2:
        if target and not k2 in target:
            continue
        if not env2[k2].term():
            continue
        if k2 not in env1:
            result[k2] = env2[k2]
    return result

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
    if te1_new.term():
        if symmetric and te2_new.term() and not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                error="Failed to merge typed expressions; result is not equal")
        return te2_new
    elif symmetric and te2_new.term():
        return te1_new
    else:
        if not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                error="Failed to merge typed expressions; result is not equal")
        return te1_new


############### Core TypedExpr objects

global _parser_assignment
_parser_assignment = None

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
    def __init__(self, op, *args, defer=False):
        """
        Constructor for TypedExpr class.  This should generally not be called
        directly, rather, the factory function should be used.  In fact,
        TypedExpr is not currently ever directly instantiated.

        This is intended only for calls from subclass `__init__`.  It (at this
        stage) amounts to a convenience function that sets some common
        variables -- a subclass that does not call this should ensure that
        these are all set.  self.args must be a list (not a tuple).

        WARNING: this function does not set self.type, which _must_ be set.
        It does not perform any type-checking.

        `defer`: annotate with this if the TypedExpr does not conform to type
        constraints.  (Useful for derivational histories or error reports.)
        """
        self.type_guessed = False
        self.derivation = None
        self.defer = defer
        self.let = False

        if (len(args) == 0):
            args = list()

        self.op = op
        self.args = list(args)

    def _type_cache_get(self, t):
        try:
            cache = self._type_adjust_cache
        except AttributeError:
            self._type_adjust_cache = dict()
            return False
        if t in cache:
            return cache[t] #.deep_copy()
        else:
            return False

    def _type_cache_set(self, t, result):
        try:
            cache = self._type_adjust_cache
        except AttributeError:
            self._type_adjust_cache = dict()
            cache = self._type_adjust_cache
        cache[t] = result


    def try_adjust_type_caching(self, new_type, derivation_reason=None,
                                            assignment=None, let_step=None):
        cached = self._type_cache_get(new_type)
        if cached is not False:
            return cached
        if let_step is not None:
            result = let_step.try_adjust_type(new_type,
                derivation_reason=derivation_reason, assignment=assignment)
            # TODO: freshen variables again here?
        else:
            result = self.try_adjust_type(new_type,
                derivation_reason=derivation_reason, assignment=assignment)
        self._type_cache_set(new_type, result)
        return result

    def try_adjust_type(self, new_type, derivation_reason=None,
                                        assignment=None):
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
            assert not isinstance(self.op, TypedExpr)
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            if self.term():
                new_term = self.copy()
                principal = env.try_add_var_mapping(new_term.op, new_type)
                if principal is None:
                    return None
                new_term._type_env = env
                new_term.type = principal
                if assignment is not None and new_term.op in assignment:
                    assignment[new_term.op] = new_term
                return derived(new_term, self, derivation_reason)
            else:
                # use the subclass' type adjustment function
                result = self.try_adjust_type_local(unify_target,
                                        derivation_reason, assignment, env)
                if result is not None:
                    result = result.under_type_assignment(env.type_mapping)
                    if result is not None:
                        result._type_env = env
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

    def try_adjust_type_local(self, unified_type, derivation_reason,
                                                            assignment, env):
        # write an error instead of throwing an exception -- this is easier for
        # the user to handle atm
        logger.error("Unimplemented `try_adjust_type_local` in class '%s'"
                                                        % type(self).__name__)
        return None

    def get_type_env(self, force_recalc=False):
        if force_recalc:
            self._type_env = self.calc_type_env(recalculate=force_recalc)
        try:
            return self._type_env
        except AttributeError:
            self._type_env = self.calc_type_env(recalculate=force_recalc)
            return self._type_env

    def calc_type_env(self, recalculate=False):
        env = TypeEnv()
        for part in self:
            if isinstance(part, TypedExpr):
                env.merge(part.get_type_env(force_recalc=recalculate))
        return env

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

    @classmethod
    def parse(cls, s, assignment=None, locals=None):
        """Attempt to parse a string `s` into a TypedExpr
        `assignment`: a variable assignment to use when parsing.
        `locals`: a dict to use as the local variables when parsing.
        """
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
            return cls.try_parse_paren_struc_r(struc, assignment=assignment,
                                                                locals=locals)

    _parsing_locals = dict()

    @classmethod
    def add_local(cls, l, value):
        cls._parsing_locals[l] = value

    @classmethod
    def del_local(cls, l):
        if l == "TypedExpr" or l == "TypedTerm":
            raise Exception("Cannot delete parsing local '%s'" % l)
        del cls._parsing_locals[l]

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
            (This is based on AIMA logic.py)
          * find things that look like term names, and surround them with calls
            to the term factory function.

        Certain special case results are wrapped in TypedExprs, e.g. sets and
        tuples.
        """
        if locals is None:
            locals = dict()

        # handle an error case: if we try to parse this, it generates a
        # SyntaxError. But if None is returned, the caller can provide a
        # context-specific error.
        if not s.strip():
            return None

        # Replace the alternative spellings of operators with canonical
        # spellings
        # TODO: derive from operator registry
        to_eval = s.replace('==>', '>>').replace('<==', '<<').replace('<=>', '%')
        to_eval = to_eval.replace('=/=', '^').replace('==', '%').replace('=>', '>>')
        lcopy = locals.copy()
        lcopy.update(cls._parsing_locals)
        pre_expansion = to_eval
        to_eval = TypedExpr.expand_terms(to_eval, assignment=assignment,
                                                            ignore=lcopy.keys())
        lcopy.update({'assignment': assignment, 'type_e': type_e})

        # cannot figure out a better way of doing this short of actually parsing
        # TODO: reimplement as a real parser, don't rely on `eval`
        global _parser_assignment
        _parser_assignment = assignment # not remotely thread-safe
        # Now eval the string.  (A security hole; do not use with an adversary.)
        try:
            result = eval(to_eval, dict(), lcopy)
        except SyntaxError as e:
            with parsing.parse_error_wrap("Binding operator parse error",
                                            s=pre_expansion):
                # try to induce some more informative error messages
                # if re.match(BindingOp.init_op_regex, pre_expansion):
                if BindingOp.init_op_match(pre_expansion):
                    BindingOp.try_parse_header(pre_expansion)
            # n.b. the msg here is probably just a placeholder, it should get
            # overridden.
            raise parsing.ParseError("Failed to parse expression", s=s, e=e)
            # other exceptions just get raised directly -- what comes up in
            # practice?
        _parser_assignment = None
        if isinstance(result, TypedExpr):
            return result
        c = from_python_container(result)
        # XX is the container check needed here? code dup with factory
        if c is not None:
            return c
        else:
            logger.warning("parse_flattened returning non-TypedExpr")
            return result

    @classmethod
    def try_parse_binding_struc(cls, s, assignment=None, locals=None,
                                                            vprefix="ilnb"):
        """Try to parse `s` as a binding operator expression.  Will return a
        subclass of BindingOp, None, or raise a `parsing.ParseError`.

        the variable on the exception `met_preconditions` is used to attempt to
        figure out whether this was a plausible attempt at a binding operator
        expression, so as to get the error message right."""
        try:
            return BindingOp.try_parse_binding_struc_r(s, assignment=assignment, locals=locals, vprefix=vprefix)
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
                s += "(" + var + ")"
                vnum += 1
                h[var] = sub_expr
        expr = cls.try_parse_flattened(s, assignment=assignment, locals=h)
        return expr


    @classmethod
    def try_parse_type(cls, s, onto=None):
        """Attempt to get a type name out of s.

        Assumes s is already stripped."""

        ts = get_type_system()
        result = ts.type_parser(s)
        return result

    @classmethod
    def try_parse_term_sequence(cls, s, lower_bound=1, upper_bound=None,
                                                        assignment=None):
        s = s.strip()
        if len(s) == 0:
            sequence = list()
            i = 0
        else:
            v, typ, i = cls.parse_term(s, i=0, return_obj=False,
                                                        assignment=assignment)
            sequence = [(v, typ)]
        if i < len(s):
            i = parsing.consume_whitespace(s, i)
            while i < len(s):
                i = parsing.consume_char(s, i, ",",
                                        "expected comma in variable sequence")
                i = parsing.consume_whitespace(s, i)
                v, typ, i = cls.parse_term(s, i=i, return_obj=False,
                                                        assignment=assignment)
                if v is None:
                    raise parsing.ParseError(
                        "Failed to find term following comma in variable sequence",
                        s=s, i=i, met_preconditions=True)
                sequence.append((v, typ))
        if lower_bound and len(sequence) < lower_bound:
            raise parsing.ParseError(
                ("Too few variables (%i < %i) in variable sequence"
                                            % (len(sequence), lower_bound)),
                s=s, i=i, met_preconditions=True)
        if upper_bound and len(sequence) > upper_bound:
            raise parsing.ParseError(
                ("Too many variables (%i > %i) in variable sequence"
                                            % (len(sequence), upper_bound)),
                s=s, i=i, met_preconditions=True)
        return sequence

    @classmethod
    def try_parse_typed_term(cls, s, assignment=None, strict=False):
        """Try to parse string 's' as a typed term.
        assignment: a variable assignment to parse s with.

        Format: n_t
          * 'n': a term name.  
            - initial numeric: term is a number.
            - initial alphabetic: term is a variable or constant.  (Variable:
              lowercase initial.)
          * 't': a type, optional.  If absent, will either get it from
            assignment, or return None as the 2nd element.

        Returns a tuple of a variable name, and a type.  If you want a
        TypedTerm, call one of the factory functions.
        
        Raises: TypeMismatch if the assignment supplies a type inconsistent
        with the specified one.
        """

        seq = cls.try_parse_term_sequence(s, lower_bound=1, upper_bound=1,
                                                        assignment=assignment)
        return seq[0]

    @classmethod
    def find_term_locations(cls, s, i=0):
        """Find locations in a string `s` that are term names."""
        # TODO: code dup with parse_term
        term_re = re.compile(r'(_?' + parsing.term_symbols_re + '+)(_)?')
        unfiltered_result = parsing.find_pattern_locations(term_re, s, i=i,
                                                                    end=None)
        result = list()
        for r in unfiltered_result:
            if r.start() > 0 and s[r.start() - 1] == ".":
                # result is prefaced by a ".", and therefore is a functional
                # call or attribute
                continue
            result.append(r)
        return result

    @classmethod
    def expand_terms(cls, s, i=0, assignment=None, ignore=None):
        """Treat terms as macros for term_factory calls.  Attempt to find all
        term strings, and replace them with eval-able factory calls.

        This is an expanded version of the original regex approach; one reason
        to move away from that is that this will truely parse the types."""
        terms = cls.find_term_locations(s, i)
        if ignore is None:
            ignore = set()
        offset = 0
        for t in terms:
            if t.start() + offset < i:
                # parsing has already consumed this candidate term, ignore.
                # (E.g. an "e" in a type signature.)
                continue
            (name, typ, end) = cls.parse_term(s, t.start() + offset,
                                    return_obj=False, assignment=assignment)
            if name is None:
                logger.warning("Unparsed term '%s'" % t.group(0)) # TODO: more?
                continue
            elif name in ignore:
                continue
            # ugh this is sort of absurd
            if typ is None:
                replace = ('TypedExpr.term_factory("%s", typ=None, assignment=assignment)' % (name))
            else:
                replace = ('TypedExpr.term_factory("%s", typ="%s", assignment=assignment)' % (name, repr(typ)))
            s = s[0:t.start() + offset] + replace + s[end:]
            i = t.start() + offset + len(replace)
            len_original = end - (t.start() + offset)
            offset += len(replace) - len_original
        return s


    @classmethod
    def parse_term(cls, s, i=0, return_obj=True, assignment=None):

        """Parse position `i` in `s` as a term expression.  A term expression
        is some alphanumeric sequence followed optionally by an underscore and
        a type.  If a type is not specified locally, but is present in 
        `assignment`, use that.  If a type is specified and is present in
        `assignment`, check type compatibility immediately."""

        ts = get_type_system()
        term_re = r'(_?' + parsing.term_symbols_re + '+)(_)?'
        term_name, next = parsing.consume_pattern(s, i, term_re,
                                                            return_match=True)
        if not term_name:
            if return_obj:
                return (None, i)
            else:
                return (None, None, i)
        if term_name.group(2):
            # try to parse a type
            # if there is a _, will force an attempt
            typ, end = ts.type_parser_recursive(s, next)
        else:
            typ = None
            end = next

        if return_obj:
            term = cls.term_factory(term_name.group(1), typ=typ,
                                    assignment=assignment, preparsed=True)
            return (term, end)
        else:
            return (term_name.group(1), typ, end)

    @classmethod
    def term_factory(cls, s, typ=None, assignment=None, preparsed=False):
        """Attempt to construct a TypedTerm from argument s.

        If s is already a TypedTerm, return a copy of the term.
        If s is a string, try to parse the string as a term name.  (see
        try_parse_typed_term)
        Otherwise, fail.
        """
        # TODO: if handed a complex TypedExpr, make a term referring to it??
        if isinstance(typ, str):
            ts = get_type_system()
            typ = ts.type_parser(typ)

        from .meta import MetaTerm
        if isinstance(s, MetaTerm):
            # MetaTerms are immutable under all operations that call this, so
            # return without copying. (The only thing that may change across
            # instances with the same value is `derivation`.)
            if typ is not None:
                s.check_type_domain(typ=typ)
            return s
        elif isinstance(s, TypedTerm):
            # todo: handle conversion to custom
            result = s.copy()
            if typ is not None:
                result = result.try_adjust_type(typ, assignment=assignment)
            return result
        else:
            if isinstance(s, str) and typ is None and not preparsed:
                # in principle, if typ is supplied, could try parsing and
                # confirm the type?
                v, typ = cls.try_parse_typed_term(s, assignment=assignment, strict=True)
            else:
                v = s
            v = utils.num_or_str(v)
            if typ is not None:
                type_vars = typ.bound_type_vars() # ??

            if not isinstance(v, str) or v.startswith("_"):
                # casting behavior when parsing: pythonic conversions between
                # type t and n in both directions. For now this is *only* in
                # parsing, so (for example) is not visited by try_adjust_type.
                if v == 0 and not isinstance(v, bool) and typ == type_t:
                    v = False
                elif types.is_numeric(v) and not isinstance(v, bool) and typ == type_t:
                    v = True
                elif v == 0 and isinstance(v, bool) and typ == type_n:
                    v = 0
                elif v == 1 and isinstance(v, bool) and typ == type_n:
                    v = 1
                return MetaTerm(v, typ=typ)

            global _constants_use_custom
            if _constants_use_custom and not is_var_symbol(v):
                return CustomTerm(v, typ=typ, assignment=assignment)
            else:
                return TypedTerm(v, typ=typ, assignment=assignment)

    @classmethod
    def factory(cls, *args, assignment=None):
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
        global _parser_assignment
        if assignment is None:
            if _parser_assignment is None:
                assignment = dict()
            else:
                assignment = _parser_assignment # not remotely thread-safe
        if len(args) == 1 and isinstance(args[0], TypedExpr):
            # handing this a single TypedExpr always returns a copy of the
            # object.  I set this case aside for clarity. subclasses must
            # implement copy() for this to work right.
            return args[0].copy()
        if len(args) == 0:
            return None #TODO something else?
        elif len(args) == 1:
            # args[0] is either an unsaturated function, a term, or a string
            # that needs parsed.
            # in the first two cases, return a unary TypedExpr
            s = args[0]
            if s in type_t.domain: # generalize using get_element_type?
                return from_python(s, type_t)
            elif s in type_n.domain:
                return from_python(s, type_n)
            elif isinstance(s, str):
                #return cls.parse_expr_string(s, assignment)
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

            # this is redundant with the constructor, but I can't currently find
            # a way to simplify. After this point, all elements of args will be
            # TypedExprs.
            remainder = tuple([cls.ensure_typed_expr(a) for a in args[1:]])

            if isinstance(args[0], str):
                global registry
                if args[0] in registry.ops:
                    # args[0] is a special-cased operator symbol
                    return op_expr_factory(*((args[0],) + remainder))

            # the only kind of operator-expression generated after this point is
            # an ApplicationExpr.
            operator = cls.ensure_typed_expr(args[0])

            # package longer arg lengths in Tuples.  After this point, there are
            # only two elements under consideration.
            if len(remainder) > 1:
                arg = Tuple(args[1:])
            else:
                arg = remainder[0]
            if (not operator.type.functional()) and operator.type_guessed:
                # special case: see if the type of the operator is guessed and
                # coerce accordingly

                # prevent future coercion of the argument
                arg.type_not_guessed()
                coerced_op = operator.try_coerce_new_argument(arg.type,
                                                        assignment=assignment)
                if coerced_op is not None:
                    logger.info(
                        "Coerced guessed type for '%s' into %s, "
                        "to match argument '%s'"
                        % (repr(operator), coerced_op.type, repr(arg)))
                    operator = coerced_op
                else:
                    logger.warning(
                        "Unable to coerce guessed type %s for '%s' "
                        "to match argument '%s' (type %s)"
                        % (operator.type, repr(operator), repr(arg), arg.type))
            result = ApplicationExpr(operator, arg, assignment=assignment)
            if result.let:
                result = derived(result.compact_type_vars(), result,
                                                            "Let substitution")
            return result

    @classmethod
    def ensure_typed_expr(cls, s, typ=None, assignment=None):
        """Coerce s to a typed expression if necessary, otherwise, return s."""
        if isinstance(s, TypedExpr):
            if assignment is not None:
                result = s.under_assignment(assignment)
            else:
                result = s
        else:
            try:
                result = cls.factory(s, assignment=assignment)
            except NotImplementedError:
                raise ValueError(
                    "Do not know how to ensure TypedExpr for '%s'" % repr(s))
        if typ is None:
            return result
        else:
            r_adjusted = result.try_adjust_type(typ, assignment=assignment)
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

        Relies on correctly implement `copy_local`.
        """
        return self.copy_local(*self)

    def copy_local(self, *args, type_check=True):
        """
        Make a copy of the element preserving everything *except* the AST.

        The default implementation calls the constructor with `args`, so if this
        isn't appropriate, you must override."""
        return type(self)(*args)

    def deep_copy(self):
        accum = list()
        for p in self:
            if isinstance(p, TypedExpr):
                accum.append(p.deep_copy())
            else:
                accum.append(p)
        return self.copy_local(*accum, type_check=False)

    def type_env(self, constants=False, target=None, free_only=True):
        env = dict()
        for part in self:
            if isinstance(part, TypedExpr):
                env = merge_type_envs(env, part.type_env(constants=constants,
                                            target=target, free_only=free_only))
        return env

    def regularize_type_env(self, assignment=None, constants=False,
                                                                target=None):
        if assignment is None:
            assignment = dict()
        env = self.get_type_env()
        return self.under_type_assignment(env.type_mapping,
                                                        merge_intersect=False)


    def compact_type_vars(self, unsafe=None, store_mapping=False):
        return let_compact_type_vars(self, unsafe=unsafe,
                                            store_mapping=store_mapping)


    def freshen_type_vars(self, target=None, unsafe=None, used_vars_only=False,
                                                        store_mapping=False):
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
        fresh_map = types.freshen_type_set(tenv, unsafe=unsafe)
        result = self.under_type_injection(fresh_map)
        result._type_env_history = history_env
        if not store_mapping:
            result.get_type_env(force_recalc=True)
        return result

    def let_type(self, typ):
        result = self.try_adjust_type(typ)
        if result is None:
            return None
        if result.let:
            result = result.compact_type_vars()
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
        r = self.copy_local(*accum, type_check=False)
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
        copy = self
        for part in copy:
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
        copy_type = copy.type.sub_type_vars(mapping)
        # Note: we still need to reset the subordinate type environments even
        # in this case.
        if copy_type == self.type and not dirty:
            return self
        result = copy.copy_local(*parts)
        if result.term():
            result.type = copy_type
        if reset:
            result.get_type_env(force_recalc=True)
        if merge_intersect:
            result._type_env = result.get_type_env().intersect_merge(
                                                TypeEnv(type_mapping=mapping))
        else:
            result._type_env = result.get_type_env().merge(
                                                TypeEnv(type_mapping=mapping))
        # need to set a derivation step for this in the calling function.
        result.derivation = self.derivation
        return result

    def under_assignment(self, assignment):
        """Use `assignment` to replace any appropriate variables in `self`."""
        # do this first so that any errors show up before the recursive step
        if assignment is None:
            a2 = dict()
        else:
            a2 = {key: self.ensure_typed_expr(assignment[key])
                                                        for key in assignment}
        return term_replace_unify(self, a2)

    # TODO: can the type env be used instead? It is effectively already
    # memoizing a superset of this information
    def free_terms(self, var_only=False):
        """Find the set of variables that are free in the typed expression.
        """
        result = set()
        # term case handled in subclass
        if isinstance(self.op, TypedExpr):
            result.update(self.op.free_terns(var_only=var_only))
        for a in self.args:
            result.update(a.free_terms(var_only=var_only))
        return result

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

    def find_safe_variable(self, starting="x", avoid_bound=True):
        """Find an a safe alpha variant of the starting point (by default: 'x'),
        that is not used in the expression."""
        blockset = self.free_variables()
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
        funtype = ts_unify(self.type, tp("<?,?>"))
        return (funtype is not None)

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
        for i in range(len(result.args)):
            # simple: go left to right, no repeats.
            new_arg_i = result.args[i].simplify_all(**sopts)
            if new_arg_i is not result.args[i]:
                result = derived(result.subst(i, new_arg_i), result,
                    desc=("Recursive simplification of subexpression %i"
                            % i),
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
        if get_sopt('reduce', sopts):
            result = result.reduce_all()
            # don't apply `reduce` recursively, it is already recursive
            sopts['reduce'] = False

        collect = get_sopt('collect', sopts) and collectable(result)
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

    def reduce(self):
        assert (not self.reducible())
        return self

    def reduce_sub(self, i):
        """Applies reduce to a constituent term, determined by argument i."""
        new_arg_i = self.args[i].reduce()
        if new_arg_i is not self.args[i]:
            result = self.copy()
            result.args[i] = new_arg_i
            if len(result.args) == 2 and isinstance(result, BindingOp):
                reason = "Reduction of body"
            else:
                reason = "Reduction of operand %s" % (i)
            return derived(result, self, desc=reason)
        return self

    def reduce_all(self):
        """Maximally reduce function-argument combinations in `self`."""

        # this is a dumb strategy: it's either not fully general (but I haven't
        # found the case yet), or it's way too inefficient, I'm not sure which;
        # probably both.  The potential overkill is the recursive step.
        # TODO: research on reduction strategies.
        # TODO: add some kind of memoization?

        # uncomment this to see just how bad this function is...
        #print("reduce_all on '%s'" % repr(self))
        result = self
        dirty = False
        for i in range(len(result.args)):
            new_arg_i = result.args[i].reduce_all()
            if new_arg_i is not result.args[i]:
                if not dirty:
                    dirty = True
                args = list(result.args)
                args[i] = new_arg_i
                next_step = result.copy_local(*args)
                if len(result.args) == 2 and isinstance(result, BindingOp):
                    reason = "Recursive reduction of body"
                else:
                    reason = "Recursive reduction of operand %s" % (i)
                result = derived(next_step, result, desc=reason,
                                                    subexpression=new_arg_i)
        self_dirty = False
        while result.reducible():
            new_result = result.reduce()
            if new_result is not result:
                dirty = True
                self_dirty = True
                result = new_result # no need to add a derivation here, reduce
                                    # will do that already
            else:
                break # should never happen...but prevent loops in case of error
        if self_dirty:
            new_result = result.reduce_all() # TODO: is this overkill?
            result = new_result
        return result


    def calculate_partiality(self, vars=None):
        condition = from_python(True)
        new_parts = list()
        for part in self:
            part_i = part.calculate_partiality(vars=vars)
            if isinstance(part_i, Partial):
                condition = condition & part_i.condition
                part_i = part_i.body
            new_parts.append(part_i)
        new_self = self.copy_local(*new_parts)
        condition = condition.simplify_all()
        if condition == from_python(True):
            intermediate = derived(Partial(new_self, condition), self,
                                                "Partiality simplification")
            return derived(new_self, intermediate, "Partiality simplification")
        else:
            return derived(Partial(new_self, condition), self,
                                                "Partiality simplification")


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
        assert not isinstance(self.op, TypedExpr)
        if not self.args:         # Constant or proposition with arity 0
            return repr(self.op)
        elif len(self.args) == 1: # Prefix operator
            return repr(self.op) + repr(self.args[0])
        else:                     # Infix operator
            return '(%s)' % (' '+self.op+' ').join([repr(a) for a in self.args])

    def latex_str(self, suppress_parens=False, **kwargs):
        """Return a representation of the TypedExpr suitable for Jupyter
        Notebook display.

        In this case the output should be pure LaTeX."""

        if not self.args:
            return ensuremath(str(self.op))
        # past this point in the list of cases should only get hard-coded
        # operators
        elif len(self.args) == 1: # Prefix operator
            return ensuremath(f"{self.op}{self.args[0].latex_str(**kwargs)}")
        else:                     # Infix operator
            base = f" {self.op} ".join([a.latex_str(**kwargs) for a in self.args])
            if not suppress_parens:
                base = f"({base})"
            return ensuremath(base)

    def _repr_latex_(self):
        return self.latex_str(suppress_parens=True)

    def __str__(self):
        if self.term():
            return self.__repr__()
        else:
            # should this just return repr unconditionally?
            return "%s, type %s" % (self.__repr__(), self.type)

    def __eq__(self, other):
        """x and y are equal iff their ops and args are equal.

        Note that this is a _syntactic_ notion of equality, not a _semantic_
        notion -- for example, two expressions would fail this notion of
        equality if one reduces to the other but that reduction has not been
        done.  Alphabetic variants will also not come out as equal."""

        # need to explicitly check this in case recursion accidentally descends into a string Op
        # TODO revisit
        if isinstance(other, TypedExpr):
            return (other is self) or (self.op == other.op and self.args == other.args and self.type == other.type)
        else:
            return False
        #TODO: equality by semantics, not syntax?

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        """Need a hash method so TypedExprs can live in dicts.

        Note that there are some special cases to worry about: ListedSets are
        not guaranteed to hash correctly.
        """
        # TODO: deal with ListedSets
        return hash(self.op) ^ hash(tuple(self.args)) ^ hash(self.type)

    def __getitem__(self, i):
        """If `i` is a number, returns a part of `self` by index.  
        index 0 always gives the operator.
        index >=1 gives whatever arguments there are.  Note that this is
        shifted from the indexing of `self.args`.

        If `i` is a TypedExpr, try to construct an expression representing
        indexing."""
        if isinstance(i, TypedExpr):
            return TupleIndex(self, i)
        else:
            return self.args[i]

    def __len__(self):
        """Return the number of parts of `self`, including the operator."""
        return len(self.args)

    # See http://www.python.org/doc/current/lib/module-operator.html
    # Not implemented: not, abs, pos, concat, contains, *item, *slice
    def __and__(self, other):    return self.factory('&',  self, other)
    def __invert__(self):        return self.factory('~',  self)
    def __lshift__(self, other): return self.factory('<<', self, other)
    def __rshift__(self, other): return self.factory('>>', self, other)
    def __or__(self, other):     return self.factory('|',  self, other)
    def __xor__(self, other):    return self.factory('^',  self, other)
    def equivalent_to(self, other): return self.factory('<=>',  self, other)
    def __mod__(self, other):    return self.equivalent_to(other)

    def __lt__(self, other):     return self.factory('<',  self, other)
    def __le__(self, other):     return self.factory('<=', self, other)
    def __ge__(self, other):     return self.factory('>=', self, other)
    def __gt__(self, other):     return self.factory('>',  self, other)
    def __add__(self, other):    return self.factory('+',  self, other)
    def __sub__(self, other):    return self.factory('-',  self, other)
    def __div__(self, other):    return self.factory('/',  self, other)
    def __truediv__(self, other):return self.factory('/',  self, other)
    def __mul__(self, other):    return self.factory('*',  self, other)
    def __neg__(self):           return self.factory('-',  self)
    def __pos__(self):           return self.factory('+',  self)
    def __pow__(self, other):    return self.factory('**', self, other)

    def __bool__(self):
        # otherwise, python tries to use the fact that these objects implement a
        # container interface to convert to bool, which can lead to weird
        # results. This is overridden in exactly one place, `MetaTerm`.
        return True


TypedExpr.add_local('TypedExpr', TypedExpr)


class ApplicationExpr(TypedExpr):
    def __init__(self, fun, arg, defer=False, assignment=None, type_check=True):
        if type_check and not defer:
            # this call may raise
            tc_result = self.fa_type_inference(fun, arg, assignment)
            if tc_result is None:
                if not fun.functional():
                    raise TypeMismatch(fun, arg,
                        error=f"Function-argument expression: `{repr(fun)}` is not a function")
                else:
                    raise TypeMismatch(fun, arg,
                        error=f"Function-argument expression: mismatched argument types `{repr(fun.type.left)}` and `{arg.type}`")
            f, a, out_type, history = tc_result
            op = "Apply"
            args = [f, a]
            self.type = out_type
        else:
            history = False
            op = "Apply"
            args = [fun, arg]
            try:
                self.type = fun.type.right
            except AttributeError:
                # the input `fun` type is not itself functional, so we can't
                # even determine the output type. Use UnknownType as a
                # placeholder.
                self.type = types.UnknownType()
        super().__init__(op, *args, defer=defer)
        if fun.let or arg.let:
            self.let = True

        if history:
            # bit of a hack: build a derivation with the deferred version as
            # the origin
            old = ApplicationExpr(fun, arg, defer=True)
            derived(self, old, desc="Type inference")    
        if isinstance(args[0], LFun):
            args[1].type_not_guessed()
        else:
            # not 100% that the following is the right fix...
            try:
                self.type_guessed = args[0].type_guessed
            except AttributeError:
                self.type_guessed = False

    def copy(self):
        return self.copy_local(self.args[0], self.args[1])

    def copy_local(self, fun, arg, type_check=True):
        result = ApplicationExpr(fun, arg, defer=self.defer,
                                                    type_check=type_check)
        result.let = self.let
        result.type_guessed = self.type_guessed
        return result

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
        """Return a string representation of the TypedExpr.

        This is guaranteed (barring bugs) to produce a parsable string that
        builds the same object.
        """
        fun = self.args[0]
        arg = self.args[1]
        if isinstance(arg, Tuple):
            arg_str = repr(arg) # tuple already generates parens
        else:
            arg_str = "(%s)" % (repr(arg))
        if isinstance(fun, CustomTerm):
            return fun.custom_appl(arg_str) # TODO: ???
        elif isinstance(fun, LFun):
            return "(%s)%s" % (repr(fun), arg_str)
        else:
            return '%s%s' % (repr(fun), arg_str)

    def try_adjust_type_local(self, new_type, derivation_reason, assignment,
                                                                        env):
        fun = self.args[0]
        arg = self.args[1]
        (new_fun_type, new_arg_type, new_ret_type) = get_type_system().unify_fr(
                            fun.type, new_type, assignment=env.type_mapping)
        if new_fun_type is None:
            return None
        new_fun = fun.try_adjust_type(new_fun_type,
                                        derivation_reason=derivation_reason,
                                        assignment=assignment)
        if new_fun is None:
            return None
        new_arg = arg.try_adjust_type(new_arg_type,
                                        derivation_reason=derivation_reason,
                                        assignment=assignment)
        if new_arg is None:
            return None
        result = self.copy_local(new_fun, new_arg, type_check=False)
        return result

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
            copy = ApplicationExpr(result, self.args[1])
            if (remove_guessed):
                result.type_guessed = False
            return copy
        else:
            return None


    @classmethod
    def fa_type_inference(cls, fun, arg, assignment):
        if fun.let:
            fun = fun.freshen_type_vars()
        if arg.let:
            arg = arg.freshen_type_vars()
        history = False
        try:
            (f_type, a_type, out_type) = get_type_system().unify_fa(fun.type, arg.type)
        except TypeMismatch as e:
            # replace pure types with the function and argument in question
            e.i1 = fun
            e.i2 = arg
            raise e
        if f_type is None:
            return None

        if fun.type != f_type:
            fun = fun.try_adjust_type_caching(f_type,
                                derivation_reason="Type inference (external)",
                                assignment=assignment)
            history = True

        if a_type != arg.type:
            arg = arg.try_adjust_type_caching(a_type,
                                derivation_reason="Type inference (external)",
                                assignment=assignment)
            history = True

        if fun.let or arg.let:
            fun, arg = let_compact_type_vars(fun, arg)
            fun.let = False
            arg.let = False
            # history?

        # assumption: by now, fun.type supports indexing to get the output type
        return (fun, arg, fun.type[1], history)

    def reducible(self):
        if (isinstance(self.args[0], LFun)
                        or isinstance(self.args[0], Disjunctive)
                        or self.args[0].type.functional()
                            and self.args[0].meta() and self.args[1].meta()):
            return True
        return False

    def reduce(self):
        """if there are arguments to op, see if a single reduction is
        possible."""
        if not self.reducible():
            return self
        else:
            result = self.args[0].apply(self.args[1])
            result.let = self.let
            return derived(result, self, desc="Reduction")

    def calculate_partiality(self, vars=None):
        # defer calculation of the argument until beta reduction has occurred
        if isinstance(self.args[0], LFun):
            return self
        else:
            return super().calculate_partiality()

    @classmethod
    def random(self, random_ctrl_fun):
        from . import test
        ftyp = get_type_system().random_from_class(types.FunType)
        fun = test.random_lfun_force_bound(ftyp, random_ctrl_fun)
        arg = random_ctrl_fun(typ=ftyp.left)
        return ApplicationExpr(fun, arg)


def common_tuple_type(t):
    elem_types = list(set(t.type))
    if len(elem_types) == 0:
        return None # could probably be better handled
    elif len(elem_types) == 1:
        ret, = elem_types
        return ret
    else:
        # this will crash if variable types are used; in principle this
        # could be allowed by concluding a variable type rather than a
        # disjunctive type
        return types.DisjunctiveType(*elem_types)


class Tuple(TypedExpr):
    """TypedExpr wrapper on a tuple.

    This works basically as a python tuple would, and is indicated using commas
    within a parenthetical. `args` is a list containing the elements of the
    tuple."""
    def __init__(self, args, typ=None, type_check=True):
        new_args = list()
        type_accum = list()
        for i in range(len(args)):
            if typ is None or not type_check:
                a_i = self.ensure_typed_expr(args[i])
            else:
                a_i = self.ensure_typed_expr(args[i], typ=typ[i])
            new_args.append(a_i)
            type_accum.append(a_i.type)
        super().__init__("Tuple", *new_args)
        self.type = types.TupleType(*type_accum)
        common_tuple_type(self) # ensure that there is a usable common type

    def copy(self):
        return Tuple(self.args)

    def copy_local(self, *args, type_check=True):
        return Tuple(args, typ=self.type)

    def index(self, i):
        return self.args[i]

    def term(self):
        return False

    def tuple(self):
        """Return a python `tuple` version of the Tuple object."""
        return tuple(self.args)

    def try_adjust_type_local(self, unified_type, derivation_reason,
                                                            assignment, env):
        content = [self.args[i].try_adjust_type(unified_type[i],
                                derivation_reason=derivation_reason,
                                assignment=assignment)
                    for i in range(len(self.args))]
        return self.copy_local(*content)

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
        return Tuple(args)



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
    """used for terms of arbitrary type.  Note that this is not exactly
    standard usage of 'term'. In general, these cover variables and constants.
    The name of the term is 'op', and 'args' is empty.

    The attribute 'type_guessed' is flagged if the type was not specified; this
    may result in coercion as necessary."""
    def __init__(self, varname, typ=None, latex_op_str=None, assignment=None,
                                    defer_type_env=False, type_check=True):
        # NOTE: does not call super
        self.op = varname
        self.derivation = None
        self.defer = False
        self.let = False
        update_a = False
        if typ is None:
            if assignment is not None and self.op in assignment:
                self.type = assignment[self.op].type
                self.type_guessed = False
            else:
                self.type = default_type(varname)
                self.type_guessed = True
        else:
            self.type_guessed = False
            self.type = typ
        if type_check and not defer_type_env: # note: cannot change type in
                                              # place safely with this code here
            env = self.calc_type_env()
            if assignment is not None:
                if self.op in assignment and typ is not None:
                    env.add_var_mapping(self.op, assignment[self.op].type)
            self.type = env.var_mapping[self.op]
            self._type_env = env

        self.suppress_type = False
        from .meta import MetaTerm
        if not isinstance(self, MetaTerm):
            if not isinstance(self.op, str):
                # note: don't use `s` parameter, because the resulting error
                # message is confusing for this specific case
                raise parsing.ParseError(
                    f"`TypedTerm` must have string operator name, got `{repr(self.op)}` (did you mean `MetaTerm`?)")

            if self.op.startswith("_"):
                raise parsing.ParseError(
                    "Invalid term name with `_` prefix for `TypedTerm` (did you mean `MetaTerm`?)",
                    s=repr(self.op))

        self.args = list()
        self.latex_op_str = latex_op_str
        if update_a:
            assignment[self.op] = self

    def copy(self):
        return TypedTerm(self.op, typ=self.type)

    def copy_local(self, type_check=True):
        result = TypedTerm(self.op, typ=self.type,
                                    latex_op_str=self.latex_op_str,
                                    type_check=type_check)
        if not type_check:
            result._type_env = self._type_env.copy()
        result.type_guessed = self.type_guessed
        return result

    def calc_type_env(self, recalculate=False):
        env = TypeEnv()
        env.add_var_mapping(self.op, self.type)
        return env

    def type_env(self, constants=False, target=None, free_only=True):
        if self.constant() and not constants:
            return set()
        if not target or self.op in target:
            return {self.op: self}
        return set()

    def free_terms(self, var_only=False):
        if not var_only or is_var_symbol(self.op):
            return {self.op}
        else:
            return set()

    def term(self):
        return True

    def apply(self, arg):
        return self(arg)

    @property
    def term_name(self):
        return self.op

    def constant(self):
        """Return true iff `self` is a constant.

        This follows the prolog convention: a constant is a term with a
        capitalized first letter.  Numbers are constants."""
        return not is_var_symbol(self.op)

    def variable(self):
        """Return true iff `self` is a variable.

        This follows the prolog convention: a variable is a term with a
        lowercase first letter."""
        return is_var_symbol(self.op)

    def __repr__(self):
        return "%s_%s" % (self.op, repr(self.type))

    def should_show_type(self, assignment=None):
        if assignment and suppress_bound_var_types:
            if self.op in assignment:
                return False
        if self.suppress_type:
            return False
        if suppress_constant_type and self.constant() and not self.meta():
            return False
        if suppress_constant_predicate_type and not self.meta():
            if (self.constant() and self.type.functional()
                            and not isinstance(self.type, types.VariableType)):
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
                                typ=self.type.add_internal_argument(typ),
                                preparsed=True)
        if not remove_guessed:
            coerced_op.type_guessed = True
        
        if assignment is not None and self.op in assignment:
            assignment[self.op] = coerced_op
        return coerced_op

    def __hash__(self):
        return hash("TypedTerm") ^ super().__hash__()

    def latex_str(self, show_types=True, assignment=None, **kwargs):
        if self.latex_op_str is None:
            op = self.op
        else:
            op = self.latex_op_str
        if not show_types or not self.should_show_type(assignment=assignment):
            return ensuremath("{%s}" % op)
        else:
            return ensuremath("{%s}_{%s}" % (op, self.type.latex_str()))

    random_term_base = {type_t : "p", type_e : "x", type_n : "n"}
    atomics = {type_t, type_e, type_n}

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
                                if (x.type==typ and x.variable() == is_var)]
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
        
        return TypedExpr.term_factory(varname, typ)


TypedExpr.add_local('TypedTerm', TypedTerm)


class CustomTerm(TypedTerm):
    """A subclass of TypedTerm used for custom displays of term names.

    The main application is for English-like metalanguage a la Heim and Kratzer.
    This isn't fully implemented as that metalanguage is actually extremely
    difficult to get right computationally..."""
    def __init__(self, varname, custom_english=None, suppress_type=True,
                 small_caps=True, typ=None, assignment=None, type_check=True):
        TypedTerm.__init__(self, varname, typ=typ, assignment=assignment,
                                                        type_check=type_check)
        self.custom = custom_english
        self.sc = small_caps
        self.suppress_type = suppress_type
        self.verbal = False
        # TODO: check type against custom string

    def copy(self):
        return CustomTerm(self.op, custom_english=self.custom,
                                   suppress_type=self.suppress_type,
                                   small_caps=self.sc,
                                   typ=self.type)

    def copy(self, op):
        return CustomTerm(op, custom_english=self.custom,
                              suppress_type=self.suppress_type,
                              small_caps=self.sc,
                              typ=self.type)

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
            if self.type == type_property:
                if self.verbal:
                    return "s"
                else:
                    return "is a"
            else:
                if self.type == type_transitive:
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
    def __init__(self, body, condition, type_check=True):
        if condition is None:
            condition = from_python(True)
        if isinstance(body, Partial):
            condition = condition & body.condition
            body = body.body
        while isinstance(condition, Partial):
            condition = condition.body & condition.condition
        condition = TypedExpr.ensure_typed_expr(condition, types.type_t)

        super().__init__("Partial", body, condition)
        self.type = body.type
        self.condition = condition
        self.body = body

    def calculate_partiality(self, vars=None):
        new_body = self.body.calculate_partiality(vars=vars)
        new_condition = self.condition.calculate_partiality(vars=vars)
        if isinstance(new_condition, Partial):
            new_condition = new_condition.body & new_condition.condition
        if isinstance(new_body, Partial):
            new_condition = new_condition & new_body.condition
            new_body = new_body.body
        new_condition = new_condition.simplify_all()
        return derived(Partial(new_body, new_condition), self,
                                                "Partiality simplification")
    
    def term(self):
        return self.body.term()

    def tuple(self):
        return tuple(self.args)
    
    def meta_tuple(self):
        return Tuple(self.args)
    
    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                    env):
        tuple_version = self.meta_tuple()
        revised_type = types.TupleType(unified_type, types.type_t)
        result = tuple_version.try_adjust_type(unified_type, derivation_reason,
                                                                assignment, env)
        return self.copy_local(result[1], result[2])
        
    def latex_str(self, suppress_parens=False, **kwargs):
        if self.condition and self.condition != from_python(True):
            return ensuremath("\\left|\\begin{array}{l}%s\\\\%s\\end{array}\\right|"
                % (self.body.latex_str(suppress_parens=True, **kwargs),
                   self.condition.latex_str(suppress_parens=True, **kwargs)))
        else:
            return ensuremath("%s" % (self.body.latex_str(suppress_parens=True, **kwargs)))

    @classmethod
    def from_Tuple(cls, t):
        if (isinstance(t, TypedExpr)
                            and (not isinstance(t, Tuple) or len(t) != 2)):
            raise parsing.ParseError(
                "Partial requires a Tuple of length 2.  (Received `%s`.)"
                % repr(t))
        return Partial(t[0], t[1])
        
    @classmethod
    def get_condition(cls, p):
        if isinstance(p, Partial) or isinstance(p, PLFun):
            return p.condition
        else:
            return from_python(True)
        
    @classmethod
    def get_atissue(cls, p):
        if isinstance(p, Partial) or isinstance(p, PLFun):
            return p.body
        else:
            return p

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        # This will implicitly use the same depth for the body and condition
        typ = get_type_system().random_type(max_type_depth, 0.5)
        body = ctrl(typ=typ)
        condition = ctrl(typ=type_t)
        return Partial(body, condition)

        
TypedExpr.add_local("Partial", Partial.from_Tuple)

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
#
# In a very roundabout way, this class acts like a dictionary mapping types to
# expressions.
class Disjunctive(TypedExpr):
    def __init__(self, *disjuncts, type_check=True):
        ts = get_type_system()
        principal_type = types.DisjunctiveType(*[d.type for d in disjuncts])
        t_adjust = set()
        # this is not a great way to do this (n*m) but I couldn't see a
        # cleverer way to catch stuff like:
        # > `Disjunctive(te("x_e"), te("y_n"), te("z_[e|t]"))`
        # It would work to not have this check here, and let the error happen
        # on type adjustment later (e.g. type adjustment to `e` would fail in
        # the above example) but I decided that that would be too confusing.
        for d in disjuncts:
            for t in principal_type:
                r = d.try_adjust_type(t)
                if r is not None:
                    if r.type in t_adjust:
                        raise parsing.ParseError(
                            "Disjoined expressions must determine unique types"
                            " (type `%s` appears duplicated in expression `%s` "
                            "for disjuncts `%s`)"
                            % (repr(t), repr(d), repr(disjuncts)))
                    else:
                        t_adjust |= {r.type}
        self.type = types.DisjunctiveType(*t_adjust)
        super().__init__("Disjunctive", *disjuncts)
        
    def copy(self):
        return Disjunctive(*self.args)
    
    def copy_local(self, *disjuncts, type_check=True):
        return Disjunctive(*disjuncts)
    
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
    
    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        ts = get_type_system()
        l = list()
        for a in self.args:
            t = ts.unify(unified_type, a.type)
            if t is None:
                continue
            l.append(a.try_adjust_type(t, derivation_reason=derivation_reason,
                                          assignment=assignment))
        assert len(l) > 0
        if (len(l) == 1):
            return l[0]
        else:
            return Disjunctive(*l)

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
    def from_tuple(cls, t):
        return Disjunctive(*t)

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

TypedExpr.add_local("Disjunctive", Disjunctive.from_tuple)




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

    # is the operation left associative without parens, i.e. for arbitrary `@`
    # does `p @ q @ r` mean `((p @ q) @ r)`?
    # this is currently just cosmetic, in that it suppresses parens for left
    # recursion on rich reprs. Essentially all python operations are left
    # associative, and the metalanguage operators inherit this behavior, so
    # it is true by default. But you could set it to False to always show
    # for some operation.
    left_assoc = True # currently just cosmetic: suppresses parens for left recursion

    # should output type be a class variable?

    def __init__(self, typ, *args, tcheck_args=True):
        if tcheck_args:
            args = [self.ensure_typed_expr(a, typ) for a in args]
        else:
            args = [self.ensure_typed_expr(a) for a in args]
        super().__init__(self.canonical_name, *args)
        self.type = typ
        if self.op_name_uni is None:
            self.op_name_uni = self.op
        # shadow the class var:
        if self.op_name_latex is None:
            self.op_name_latex = self.op_name_uni

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, type_check=True):
        """This must be overriden by classes that are not produced by the
        factory."""
        # TODO: is this necessary?
        return op_expr_factory(self.op, *args)

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
            # XX left assoc parens?
            p.text("(")
            for a in self.args[0:-1]:
                p.pretty(self.args[0])
                p.text(" %s " % self.op_name_uni)
            p.pretty(self.args[-1])
            p.text(")")

    def __str__(self):
        return "%s\nType: %s" % (repr(self), self.type)

    def __repr__(self):
        if self.arity == 1:
            if (self.operator_style):
                return "%s%s" % (self.op, repr(self.args[0]))
            else:
                return "%s(%s)" % (self.op, repr(self.args[0]))
        else:
            op_text = " %s " % self.op
            return "(%s)" % (op_text.join([repr(a) for a in self.args]))

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
            if (self.operator_style):
                return ensuremath("%s %s" % (self.op_name_latex,
                    self._sub_latex_str(0, **kwargs)))
            else:
                return ensuremath("%s(%s)" % (self.op_name_latex,
                    self._sub_latex_str(0, suppress_parens=True, **kwargs)))
        else:
            sub_parens = True
            inner = f" {self.op_name_latex} ".join(
                [self._sub_latex_str(i, **kwargs) for i in range(len(self.args))])
            if not suppress_parens:
                inner = f"({inner})"
            return ensuremath(inner)

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
        return cls(*[ctrl(typ=type_t) for a in range(cls.arity)])


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
    if p is True and (typ is None or typ == type_t):
        return true_term
    elif p is False and (typ is None or typ == type_t):
        return false_term
    else:
        # this will raise if there is no known type domain for python objects
        # of p's type
        from .meta import MetaTerm
        return MetaTerm(p, typ=typ)


def from_python_container(p):
    from .sets import sset
    # can this use collections.abc types?
    if isinstance(p, tuple):
        # should an empty tuple force a MetaTerm?
        return Tuple(p)
    elif isinstance(p, set):
        return sset(p)
    elif isinstance(p, dict) and len(p) == 0:
        # hack: empty dict is treated as empty set, so that "{}" makes sense
        return sset(set())
    return None


def to_python_container(e):
    from .sets import ListedSet
    if isinstance(e, ListedSet):
        return e.set()
    elif isinstance(e, Tuple):
        return e.tuple()
    elif e.meta() and (
                isinstance(e.type, types.SetType)
                or isinstance(e.type, types.FunType)
                or isinstance(e.type, types.TupleType)):
        return e.op
    return None


# decorator for wrapping simplify functions, see examples in `meta.number`.
# TODO: this could be generalized a further...
def op(op, arg_type, ret_type,
            op_uni=None, op_latex=None, deriv_desc=None,
            python_only=True):
    if deriv_desc is None:
        deriv_desc = op_uni and op_uni or op

    def op_decorator(func):
        # we will pass `self` to func, so allow an extra param for it
        arity = len(inspect.signature(func).parameters) - 1

        # constructs a subclass of either Syncat
        if not (arity == 1 or arity == 2):
            raise ValueError("@op needs function of arity 1 or 2 (got %d)" % arity)
        class WrappedOp(SyncatOpExpr):
            def __init__(self, *args):
                # XX this updates __name__ but not __class__
                functools.update_wrapper(self, func)
                if len(args) != arity:
                    # what exception type to use here?
                    raise parsing.ParseError(
                        "%s (%s) needs %d operands but %d were given"
                        % (op_uni, func.__name__, arity, len(args)))
                args = [self.ensure_typed_expr(a, arg_type) for a in args]
                self.operator_style = True
                super().__init__(ret_type, *args, tcheck_args=False)

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
                args = [ctrl(typ=arg_type) for i in range(arity)]
                return cls(*args)

        WrappedOp.arity = arity
        WrappedOp.canonical_name = op
        WrappedOp.op_name_uni = op_uni
        WrappedOp.op_name_latex = op_latex

        # some metaprogramming to get nicer reprs for the class object. If we
        # don't overwrite these, the repr will show something like:
        # `lamb.meta.core.op.<locals>.op_decorator.<locals>.WrappedOp`,
        # which is of course completely unhelpful. The builtin (C) repr for
        # `type` uses specifically __module__ and __qualname__. Because `func`
        # here is the decorated function, using its `__qualname__` gets the
        # exact right reference to the class produced, e.g.
        # `lamb.meta.boolean.UnaryNegExpr`. (An alternative here that might be
        # clearer would be to use a metaclass; but as of py3.3 I don't think
        # the python internals this is relying on are likely to change...)
        WrappedOp.__name__ = func.__name__
        WrappedOp.__qualname__ = func.__qualname__
        WrappedOp.__module__ = func.__module__
        return WrappedOp
    return op_decorator


# probably belongs elsewhere
class BinaryGenericEqExpr(SyncatOpExpr):
    canonical_name = "<=>"
    op_name_latex = "="
    commutative = True
    # note: this associativity here is fairly in principle, since it only
    # applies at type t, and type t has a special case implementation in a
    # different class...
    associative = True

    """Type-generic equality.  This places no constraints on the type of `arg1`
    and `arg2` save that they be equal."""
    def __init__(self, arg1, arg2):
        self.argtype = ts_unify_with(arg1, arg2,
                                error="Equality requires compatible types")
        arg1 = self.ensure_typed_expr(arg1, self.argtype)
        # maybe raise the exception directly?
        arg2 = self.ensure_typed_expr(arg2, self.argtype)
        # some problems with equality using '==', TODO recheck, but for now
        # just use "<=>" in the normalized form
        super().__init__(type_t, arg1, arg2, tcheck_args = False)

    def simplify(self, **sopts):
        if (self.args[0].op in self.argtype.domain
                            and self.args[1].op in self.argtype.domain):
            # equality check on elements of the underlying type domain
            return derived(te(self.args[0].op == self.args[1].op),
                                                    self, desc="Equality")
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

    @classmethod
    def check_viable(cls, *args):
        if len(args) != 2:
            return False
        principal_type = ts_unify(args[0].type, args[1].type)
        # leave type t to the simply-typed biconditional operator
        # TODO: it should be possible to handle this in a more generalized way
        return (principal_type is not None
            and principal_type != type_t
            and not isinstance(principal_type, types.SetType))


class TupleIndex(SyncatOpExpr):
    arity = 2
    canonical_name = "[]" # not a normal SyncatOpExpr!
    commutative = False

    def __init__(self, arg1, arg2, type_check=True):
        arg1 = self.ensure_typed_expr(arg1)
        if not isinstance(arg1.type, types.TupleType):
            raise types.TypeMismatch(arg1, arg2,
                    error="Tuple indexing expression with a non-tuple")
        arg2 = self.ensure_typed_expr(arg2, types.type_n)
        if arg2.op in types.type_n.domain:
            try:
                # this effectively enforces an undeclared subtype of type_n
                # based on the following exceptions
                output_type = arg1.type[arg2.op]
            except IndexError:
                # XX this isn't really a type mismatch...
                raise TypeMismatch(arg1, arg2,
                    error="Tuple indexing expression with out-of-range index")
            except TypeError:
                # XX this isn't really a type mismatch...
                raise TypeMismatch(arg1, arg2,
                    error="Tuple indexing expression with invalid index")
        else:
            # we don't know which element will be selected; get a potentially
            # disjunctive type for the whole expression
            output_type = common_tuple_type(arg1)
        super().__init__(output_type, arg1, arg2, tcheck_args=False)

    def copy(self):
        return TupleIndex(self.args[0], self.args[1])

    def copy_local(self, arg1, arg2, type_check=True):
        return TupleIndex(arg1, arg2)

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        if self.args[1].op in types.type_n.domain:
            ttype = list(self.args[0].type)
            ttype[self.args[1].op] = unified_type
            adjusted_tuple = self.args[0].try_adjust_type(
                                                    types.TupleType(*ttype))
            return self.copy_local(adjusted_tuple, self.args[1])
        else:
            logger.warning(
                "Using non-constant index; not well-supported at present.")
            return None

    def __str__(self):
        return "%s\nType: %s" % (repr(self), self.type)

    def __repr__(self):
        return "(%s[%s])" % (repr(self.args[0]), repr(self.args[1]))

    def latex_str(self, suppress_parens=False, **kwargs):
        return ensuremath("(%s[%s])" % (self.args[0].latex_str(**kwargs),
                                        self.args[1].latex_str(**kwargs)))

    def reduce(self):
        if self.args[1] in types.type_n.domain:
            # args[1] is a numeric MetaTerm
            if isinstance(self.args[0], Tuple):
                result = self.args[0].tuple()[self.args[1].op].copy()
                return derived(result, self, "Resolution of index")
            elif self.args[0].meta():
                # XX this code should be on the tuple object somehow
                result = term(self.args[0].op[self.args[1].op])
                return derived(result, self, "Resolution of index")
            # else fallthrough: non-meta term of a tuple type
        # else fallthrough: index that is not a metaterm
        return self

    def reducible(self):
        if (self.args[1] in types.type_n.domain
                and (isinstance(self.args[0], Tuple) or self.args[0].meta())):
            return True
        # no support for non-constant indices at present, not even ones that
        # should be mathematically simplifiable
        return False

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

    @classmethod
    def binding_op_precheck(self, op_class, var_list):
        for i in range(len(var_list)):
            if not is_var_symbol(var_list[i][0]):
                raise parsing.ParseError(
                    "Need variable name in binding operator expression"
                    " (received `%s`)" % var_list[i][0], None)
        if (not op_class.allow_multivars) and len(var_list) > 1:
            raise parsing.ParseError(
                "Operator class `%s` does not allow >1 variables"
                % (op_class.canonical_name), None)
        if (not op_class.allow_novars) and len(var_list) == 0:
            raise parsing.ParseError(
                "Operator class `%s` does not allow 0 variables"
                % (op_class.canonical_name), None)

    @classmethod
    def binding_op_factory(cls, op_class, var_list, body, assignment=None):
        cls.binding_op_precheck(op_class, var_list)
        for i in range(len(var_list)):
            if var_list[i][1] is None:
                var_list[i] = (var_list[i][0],
                                default_variable_type(var_list[i][0]))
        if op_class.allow_multivars or op_class.allow_novars:
            # use alternate constructor
            # TODO: unify these constructors
            return op_class(var_list, body, assignment=assignment)
        else:
            return op_class(var_or_vtype=var_list[0][1],
                            varname=var_list[0][0],
                            body=body,
                            assignment=assignment)

    def __init__(self, var_or_vtype, typ, body, varname=None, body_type=None,
                                        assignment=None, type_check=True):
        # NOTE: not calling superclass
        # Warning: can't assume in general that typ is not None. 
        # I.e. may be set in subclass after a call
        # to this function.  Subclass is responsible for doing this properly...
        if body_type is None:
            body_type = typ
        if isinstance(var_or_vtype, str):
            var_or_vtype = TypedExpr.term_factory(var_or_vtype)
        if isinstance(var_or_vtype, TypedTerm):
            if varname is not None:
                logger.warning("Overriding varname '%s' with '%s'"
                                            % (varname, var_or_vtype.op))
            varname = var_or_vtype.op
            vartype = var_or_vtype.type
        elif types.is_type(var_or_vtype):
            if varname is None:
                varname = self.default_varname()
            vartype = var_or_vtype
        else:
            logger.error("Unknown var_or_vtype: " + repr(var_or_vtype))
            raise NotImplementedError
        if not is_var_symbol(varname):
            raise ValueError("Need variable name (got '%s')" % varname)
        if typ is not None:
            self.type = typ
        self.derivation = None
        self.type_guessed = False
        self.defer = False
        self.let = False
        self.init_args()
        self.init_var(varname, vartype)
        # TODO: consider overriding __eq__ and __hash__.
        if type_check:
            sassign = self.scope_assignment(assignment=assignment)
            try:
                self.init_body(self.ensure_typed_expr(body, body_type,
                                                        assignment=sassign))
            except types.TypeMismatch as e:
                e.error = f"Failed to ensure body type {body_type} for operator class `{self.canonical_name}`"
                raise e
            body_env = self.body.get_type_env()
            if self.varname in body_env.var_mapping: # binding can be vacuous
                if body_env.var_mapping[self.varname] != self.vartype:
                    # propagate type inference to binding expression
                    new_vartype = body_env.var_mapping[self.varname]
                    assert new_vartype is not None
                    self.init_var(self.varname, new_vartype)
            self.init_body(self.body.regularize_type_env())
            self.init_var_by_instance(
                self.var_instance.under_type_assignment(body_env.type_mapping,
                                                        merge_intersect=False))
        else:
            self.init_body(body)

    def copy_local(self, *args, type_check=True):
        return type(self)(*args, type_check=type_check)

    def scope_assignment(self, assignment=None):
        if assignment is None:
            assignment = dict()
        else:
            assignment = assignment.copy()
        assignment[self.varname] = self.var_instance
        return assignment

    def default_varname(self):
        return "x"

    def init_args(self):
        try:
            a = self.args
        except AttributeError:
            self.args = list([None, None])
        assert len(self.args) == 2

    def init_var(self, name=None, typ=None):
        self.init_args()
        if name is None:
            if typ is None:
                raise ValueError
            else:
                var_instance = TypedTerm(self.varname, typ)
        else:
            if typ is None:
                var_instance = TypedTerm(name, self.var_instance.type)
            else:
                var_instance = TypedTerm(name, typ)
        self.args[0] = var_instance
        self.op = "%s:" % (self.canonical_name)


    def init_var_by_instance(self, v):
        self.init_var(v.op, v.type)

    def init_body(self, b):
        self.init_args()
        self.args[1] = b

    @property
    def varname(self):
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
        if BindingOp.init_op_match:
            # TODO: is there a clever way to do this with a single match group
            match = re.match(BindingOp.init_op_regex, s)
            if match:
                if match.group(2):
                    return match.group(2), match.end(2)
                else:
                    return match.group(1), match.end(1)
        return None

    def alpha_convert(self, new_varname):
        """Produce an alphabetic variant of the expression w.r.t. the bound
        variable, with new_varname as the new name.

        Returns a copy.  Will not affect types of either the expression or the
        variables."""
        new_self = self.copy()
        new_self.init_body(variable_convert(self.body, {self.varname: new_varname}))
        new_self.init_var(name=new_varname)
        return new_self

    def latex_op_str(self):
        return self.latex_op_str_short()

    def latex_op_str_short(self):
        return "%s %s_{%s} \\: . \\:" % (self.op_name_latex, 
                                                self.varname, 
                                                self.vartype.latex_str())

    def __str__(self):
        return "%s %s : %s, Type: %s" % (self.op_name, self.varname,
                                            repr(self.body), self.type)

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
        sub_env = self.body.get_type_env(force_recalc=recalculate).copy()
        # ensure any variable types introduced by the variable show up even if
        # they are not present in the subformula
        sub_env.add_type_to_var_set(self.var_instance.type)
        if self.varname in sub_env.var_mapping:
            del sub_env.var_mapping[self.varname]
        return sub_env

    def type_env(self, constants=False, target=None, free_only=True):
        sub_env = self.body.type_env(constants=constants, target=target,
                                                        free_only=free_only)
        if free_only and self.varname in sub_env: # binding can be vacuous
            del sub_env[self.varname]
        return sub_env


    def vacuous(self):
        """Return true just in case the operator's variable is not free in the
        body expression."""
        return self.varname in super().free_variables()

    def term(self):
        return False

    def project_partiality_strict(b, body, condition):
        # refactor somehow?
        from .sets import ConditionSet
        from .boolean import ForallUnary
        b_cls = type(b)
        if isinstance(b, ConditionSet) or isinstance(b, LFun):
            return b
        else: # IotaPartial handled in subclass
            return Partial(b_cls(b.var_instance, body),
                                            ForallUnary(b.var_instance, body))

    def project_partiality_weak(b, body, condition):
        # refactor somehow?
        from .sets import ConditionSet
        from .boolean import ForallUnary, ExistsUnary, IotaUnary, ExistsExact
        b_cls = type(b)
        if isinstance(b, ForallUnary):
            return Partial(b_cls(b.var_instance, body),
                                            b_cls(b.var_instance, condition))
        elif isinstance(b, ExistsUnary) or isinstance(b, ExistsExact):
            return Partial(b_cls(b.var_instance, body & condition),
                                            b_cls(b.var_instance, condition))
        elif isinstance(b, IotaUnary): # does this lead to scope issues for the condition?
            return Partial(b_cls(b.var_instance, body & condition),
                                        ExistsUnary(b.var_instance, condition))
        elif isinstance(b, ConditionSet) or isinstance(b, LFun):
            return b
        else: # IotaPartial handled in subclass
            # is this really a type issue?
            raise TypeMismatch(b, None,
                    error="No implemented way of projecting partiality for BindingOp %s"
                    % repr(type(b).__name__))

    def calculate_partiality(self, vars=None):
        if vars is None:
            vars = set()
        if isinstance(self, LFun):
            vars |= {self.varname}

        # defer any further calculation if there are bound variables in the body
        if vars & self.body.free_variables():
            return self

        new_body = self.body.calculate_partiality(vars=vars)
        if isinstance(new_body, Partial):
            if new_body.condition == from_python(True):
                return derived(self.copy_local(self.var_instance, new_body),
                                            self, "Partiality simplification")
            if self.varname in new_body.condition.free_variables():
                if BindingOp.partiality_weak:
                    return derived(
                        self.project_partiality_weak(new_body.body,
                                                     new_body.condition),
                        self, "Partiality simplification")
                else:
                    return derived(
                        self.project_partiality_strict(new_body.body,
                                                       new_body.condition),
                        self, "Partiality simplification")
            else:
                new_condition = new_body.condition
                new_self = self.copy_local(self.var_instance, new_body.body)
                return derived(Partial(new_self, new_condition), self,
                    "Partiality simplification")
        else:
            return derived(self.copy_local(self.var_instance, new_body), self,
                "Partiality simplification")

    @classmethod
    def try_parse_header(cls, s, assignment=None, locals=None):
        """Try and parse the header of a binding operator expression, i.e.
        everything up to the body including ':'.

        If this succeeds, it will return a tuple with the class object, the
        variable name, the variable type, and the string after the ':'' if any.

        If it fails, it will either return None or raise an exception.  That
        exception is typically a ParseError.
        """

        global registry

        i = 0
        # if BindingOp.init_op_regex is None:
        #     return None # no operators to parse
        # op_match = re.match(BindingOp.init_op_regex, s)
        op_match = cls.init_op_match(s)
        if not op_match:
            raise parsing.ParseError(
                "Unknown operator when trying to parse binding operator expression",
                s, None, met_preconditions=False)
        op_name, i = op_match

        if op_name in registry.canonicalize_binding_ops:
            op_name = registry.canonicalize_binding_ops[op_name]
        if op_name not in registry.binding_ops:
            raise Exception(
                "Can't find binding operator '%s'; should be impossible"
                % op_name)
        op_class = registry.binding_ops[op_name]

        split = s.split(":", 1)
        header = split[0]
        vname = header[i:].strip() # removes everything but a variable name
        try:
            var_seq = cls.try_parse_term_sequence(vname, lower_bound=None,
                                    upper_bound=None, assignment=assignment)
            cls.binding_op_precheck(op_class, var_seq)
        except parsing.ParseError as e:
            # somewhat involved logic: try to parse the var sequence before
            # reporting errors about a missing `:`. However, if we are missing
            # a `:`, mark `met_preconditions` as false so that the parser isn't
            # committed to a binding op header.
            if len(split) != 2:
                e.met_preconditions = False
            raise e
        if (len(split) != 2):
            # possibly should change to met_preconditions = True in the future.
            # At this point, we have seen a binding expression token.
            raise parsing.ParseError(
                "Missing ':' in binding operator expression", s, None,
                met_preconditions=False)
        return (op_class, var_seq, split[1])

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

        if (len(struc) == 0):
            return None
        if isinstance(struc[0], str) and struc[0] in parsing.brackets:
            potential_header = struc[1]
            bracketed = True
        else:
            potential_header = struc[0]
            bracketed = False
        if not isinstance(potential_header, str):
            return None
        result = BindingOp.try_parse_header(potential_header)
        if result is None:
            return None
        (op_class, var_list, remainder) = result
        # remainder is any string left over from parsing the header.
        if bracketed:
            # note: syntax checking for bracket matching is already done, this
            # does not need to check for that here.
            assert(parsing.brackets[struc[0]] == struc[-1])
            new_struc = [remainder,] + struc[2:-1]
        else:
            new_struc = [remainder,] + struc[1:]
        if assignment is None: 
            assignment = dict()
        else:
            assignment = assignment.copy()
        store_old_v = None
        for var_tuple in var_list:
            (v,t) = var_tuple
            assignment[v] = TypedTerm(v, t)
        body = None
        with parsing.parse_error_wrap(
                        "Binding operator expression has unparsable body",
                        paren_struc=struc):
            body = TypedExpr.try_parse_paren_struc_r(new_struc,
                        assignment=assignment, locals=locals, vprefix=vprefix)

        if body is None:
            raise parsing.ParseError(
                "Can't create body-less binding operator expression",
                parsing.flatten_paren_struc(struc), None)

        with parsing.parse_error_wrap("Binding operator parse error",
                                    paren_struc=struc):
            result = BindingOp.binding_op_factory(op_class, var_list, body,
                assignment=assignment)
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
    def random(cls, ctrl, body_type=type_t, max_type_depth=1):
        from . import test
        var_type = get_type_system().random_type(max_type_depth, 0.5)
        variable = test.random_term(var_type, usedset=test.random_used_vars,
                                                prob_used=0.2, prob_var=1.0)
        test.random_used_vars |= {variable}
        return cls(variable, ctrl(typ=type_t))


class LFun(BindingOp):
    """A typed function.  Can itself be used as an operator in a TypedExpr.

    """
    canonical_name = "Lambda"
    secondary_names = {"L", "λ", "lambda"}
    op_name_uni="λ"
    op_name_latex="\\lambda{}"
    commutative = False
    left_commutative = False

    def __init__(self, var_or_vtype, body, varname=None, let=False,
                                            assignment=None, type_check=True):
        # Use placeholder typ argument of None.  This is because the input type
        # won't be known until the var_or_vtype argument is parsed, which is
        # done in the superclass constructor.
        # sort of a hack, this could potentially cause odd side effects if
        # BindingOp.__init__ is changed without taking this into account.
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body,
            varname=varname, body_type=body.type, assignment=assignment,
            type_check=type_check)
        self.type = FunType(self.vartype, body.type)
        self.let = let

    @property
    def argtype(self):
        return self.type.left

    @property
    def returntype(self):
        return self.type.right

    def functional(self):
        return True # no need to do any calculations

    def copy(self):
        r = LFun(self.argtype, self.body, self.varname, type_check=False)
        r.let = self.let
        return r

    def copy_local(self, var, arg, type_check=True):
        r = LFun(var, arg, type_check=type_check)
        r.let = self.let
        return r

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        vacuous = False
        # env will not start with bound variable in it
        env.add_var_mapping(self.varname, self.argtype)
        # update mapping with new type
        left_principal = env.try_add_var_mapping(self.varname,
                                                            unified_type.left)
        if left_principal is None:
            return None
        new_body = self.body
        if self.argtype != left_principal:
            # arg type needs to be adjusted.
            new_var = TypedTerm(self.varname, left_principal)
        else:
            new_var = self.var_instance

        if self.type.right != unified_type.right:
            new_body = new_body.try_adjust_type(unified_type.right,
                                            derivation_reason=derivation_reason,
                                            assignment=assignment)
        new_fun = self.copy_local(new_var, new_body)
        env.merge(new_body.get_type_env())
        if self.varname in env.var_mapping:
            del env.var_mapping[self.varname]
        new_fun = new_fun.under_type_assignment(env.type_mapping)
        return new_fun     

    def apply(self,arg):
        """Apply an argument directly to the function.

        `__call__` plus `reduce` is (almost) equivalent to `apply`, but using
        `apply` directly will not generate a derivations."""

        # do I really want flexible equality here??
        # TODO: return to this.  Right now a type mismatch still gets raised
        # during beta reduction.
        ts = get_type_system()
        if ts.eq_check(self.argtype, arg.type):
            # first check for potential variable name collisions when
            # substituting, and the substitute
            #TODO: do I want to actually return the result of alpha converting?
            # May be needed later?
            new_self = alpha_convert(self, unsafe_variables(self, arg))
            # TODO: the copy here is a hack.  Right now identity functions
            # otherwise result in no copying at all, leading to very
            # wrong results.  This needs to be tracked down to its root and
            # fixed.
            return (beta_reduce_ts(new_self.body, new_self.varname, arg)).copy()
        else:
            raise TypeMismatch(self, arg, error="Function-argument application: mismatched argument type")

    def compose(self, other):
        """Function composition."""
        return fun_compose(self, other)

    def __mul__(self, other):
        """Override `*` as function composition for LFuns.  Note that this
        _only_ works for LFuns currently, not functional constants/variables."""
        return self.compose(other)

    @classmethod
    def random(self, ctrl):
        from . import test
        # not great at reusing bound variables
        ftyp = get_type_system().random_from_class(types.FunType)
        return test.random_lfun(ftyp, ctrl)

def geach_combinator(gtype, ftype):
    body = term("g", gtype)(term("f", ftype)(term("x", ftype.left)))
    combinator = LFun(gtype, LFun(ftype,
                LFun(ftype.left, body,varname="x"),varname="f"), varname="g")
    return combinator

def fun_compose(g, f):
    """Function composition using the geach combinator for the appropriate type,
    defined above."""
    if (not (g.type.functional() and f.type.functional()
             and g.type.left == f.type.right)):
        raise types.TypeMismatch(g, f,
                        error="Function composition type constraints not met")
    combinator = geach_combinator(g.type, f.type)
    result = (combinator(g)(f)).reduce_all()
    return result

