#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re, logging, random
from numbers import Number
from lamb import types, utils, parsing, display
from lamb.types import TypeMismatch, type_e, type_t, type_n
from lamb.types import type_property, type_transitive, BasicType, FunType
from lamb.utils import *

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

global _parser_assignment
_parser_assignment = None

def constants_use_custom(v):
    """Set whether constants use custom display routines."""
    global _constants_use_custom
    _constants_use_custom = v

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
    ts = get_type_system()
    return ts.unify(a, b)

global unify
unify = ts_unify

def ts_compatible(a, b):
    """Returns `True` or `False` depending on whether `a` and `b` are
    compatible types."""
    ts = get_type_system()
    return ts.unify(a,b) is not None

def check_type(item, typ, raise_tm=True, msg=None):
    ts = get_type_system()
    if not ts.eq_check(item.content.type, typ):
        if raise_tm:
            raise types.TypeMismatch(item, typ, msg)
        else:
            return None
    else:
        return item


def tp(s):
    """Convenience wrapper for the current type system's type parser."""
    ts = get_type_system()
    result = ts.type_parser(s)
    return result

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

def term(s, typ=None, assignment=None):
    """Convenience wrapper for building terms.
    `s`: the term's name.
    `typ`: the term's type, if specified."""
    return TypedTerm.term_factory(s, typ=typ, assignment=assignment)

_type_system = types.poly_system

unary_tf_ops = set(['~'])
binary_tf_ops = set(['>>', '<<', '&', '|', '<=>', '%'])
tf_ops = unary_tf_ops | binary_tf_ops

unary_num_ops = set(['-'])
binary_num_rels = set(['<', '<=', '>=', '>'])
binary_num_ops = {'+', '-', '/', '*', '**'}
num_ops = unary_num_ops | binary_num_ops | binary_num_rels

basic_ops = tf_ops | num_ops

basic_ops_to_latex = {
    "&": "\\wedge{}",
    "|": "\\vee{}",
    "~": "\\neg{}",
    ">>": "\\rightarrow{}"
}

def text_op_in_latex(op):
    if op in basic_ops_to_latex:
        return basic_ops_to_latex[op]
    return op

global partiality_analysis, partiality_strict, partiality_weak
partiality_strict = "strict"
partiality_weak = "weak"
partiality_analysis = partiality_weak


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
                    "Failed to unify types across distinct instances of term")
        return result

    def try_add_var_mapping(self, vname, typ):
        ts = get_type_system()
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
        result = ts.unify_details(t1, t2, assignment=self.type_mapping)
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
        if not defer:
            self.update_type_vars()
        return principal

    def add_type_mapping(self, type_var, typ, defer=False):
        principal = self.try_add_type_mapping(type_var, typ, defer=defer)
        if principal is None:
            raise TypeMismatch(self.type_mapping[type_var], typ,
                "Failed to unify type variable %s across contexts" % type_var)
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
            unify = ts.unify(env1[k1].type, env2[k1].type)
            if unify is None:
                raise TypeMismatch(env1[k1], env2[k1],
                    "Failed to unify types across distinct instances of term")
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
    ts = get_type_system()
    principal = ts.unify(te1.type, te2.type)
    # TODO: these error messages are somewhat cryptic
    if principal is None:
        raise TypeMismatch(te1, te2,
                "Failed to merge typed expressions (incompatible types)")
    te1_new = te1.try_adjust_type(principal)
    te2_new = te2.try_adjust_type(principal)
    if te1_new is None or te2_new is None:
        raise TypeMismatch(te1, te2,
                "Failed to merge typed expressions (type adjustment failed)")
    if te1_new.term():
        if symmetric and te2_new.term() and not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                "Failed to merge typed expressions; result is not equal")
        return te2_new
    elif symmetric and te2_new.term():
        return te1_new
    else:
        if not (te1_new == te2_new):
            raise TypeMismatch(te1, te2,
                "Failed to merge typed expressions; result is not equal")
        return te1_new

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
        unified = ts.unify(s.type, old.type) # order matters: prioritize type
                                             # variables from the substitution
        if unified is None:
            raise TypeMismatch(s, old, "Substitution for element %s of '%s'"
                                                            % (i, repr(self)))
        if unified != s.type:
            # compatible but unify suggested a new type for the substitution.  
            # Try adjusting the type of the expression.
            s_a = s.try_adjust_type(unified)
            if s_a is None:
                raise TypeMismatch(s, old, "Substitution for element %s of '%s'"
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
        # Replace the alternative spellings of operators with canonical
        # spellings
        to_eval = s.replace('==>', '>>').replace('<==', '<<')
        to_eval = to_eval.replace('<=>', '%').replace('=/=', '^').replace('==', '%')
        lcopy = locals.copy()
        lcopy.update(cls._parsing_locals)
        to_eval = TypedExpr.expand_terms(to_eval, assignment=assignment,
                                                            ignore=lcopy.keys())
        # Now eval the string.  (A security hole; do not use with an adversary.)
        lcopy.update({'assignment': assignment, 'type_e': type_e})

        # cannot figure out a better way of doing this short of actually parsing
        # TODO: reimplement as a real parser, don't rely on `eval`
        global _parser_assignment
        _parser_assignment = assignment # not remotely thread-safe
        try:
            result = eval(to_eval, dict(), lcopy)
        except SyntaxError as e:
            raise parsing.ParseError("Failed to parse expression", s=s, e=e)
            # other exceptions just get raised directly -- what comes up in
            # practice?
        _parser_assignment = None
        if isinstance(result, tuple):
            return Tuple(result)
        elif isinstance(result, set):
            return ListedSet(result)
        elif isinstance(result, dict) and len(result) == 0:
            # hack: empty dict is treated as empty set, so that "{}" makes sense
            return ListedSet(set())
        elif isinstance(result, TypedExpr):
            return result
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
        term_re = re.compile(r'([a-zA-Z0-9]+)(_)?')
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
        term_name, next = parsing.consume_pattern(s, i, r'([a-zA-Z0-9]+)(_)?',
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
        if (isinstance(s, TypedTerm)):
            # todo: handle conversion to custom
            result = s.copy()
            if typ is not None:
                result = result.try_adjust_type(typ, assignment=assignment)
            return result
        elif (isinstance(s, str)):
            if typ is None and not preparsed:
                v, typ = cls.try_parse_typed_term(s, assignment=assignment, strict=True)
            else:
                v = s
            v = num_or_str(v)
            if typ is not None:
                type_vars = typ.bound_type_vars()
            if _constants_use_custom and not is_var_symbol(v):
                return CustomTerm(v, typ=typ, assignment=assignment)
            else:
                return TypedTerm(v, typ=typ, assignment=assignment)
        else:
            raise NotImplementedError

    @classmethod
    def factory(cls, *args, assignment=None):
        """Factory method for TypedExprs.  Will return a TypedExpr or subclass.

        Special cases:
          * single arg, is a TypedExpr: will return a copy of that arg.  (See
            ensure_typed_expr for alternate semantics.)
          * single arg, is a number: will return a TypedTerm using that number.
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
            if s is True:
                return true_term
            elif s is False:
                return false_term
            elif isinstance(s, Number): 
                return TypedTerm(s, type_n)
            elif isinstance(s, str):
                #return cls.parse_expr_string(s, assignment)
                return cls.parse(s, assignment)
            else:
                raise NotImplementedError
        else:
            # Argument length > 1.  
            # This code path is for constructing complex TypedExprs where
            # args[0] must be a function / operator. Will potentially recurse
            # via ensure_typed_expr on all arguments.

            if isinstance(args[0], str):
                if args[0] in op_symbols:
                    # args[0] is a special-cased operator symbol
                    return op_expr_factory(*args)

            # the only kind of operator-expression generated after this point is
            # an ApplicationExpr.
            operator = cls.ensure_typed_expr(args[0])

            # this is redundant with the constructor, but I can't currently find
            # a way to simplify. After this point, all elements of args will be
            # TypedExprs.
            remainder = tuple([cls.ensure_typed_expr(a) for a in args[1:]])

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
                raise TypeMismatch(result, typ, mode="type adjustment")
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


    def compact_type_vars(self, target=None, unsafe=None, used_vars_only=True,
                                                        store_mapping=False):
        """Compact the type variables on `self` into X variables with a low
        number.  By default this will not store the mapping that resulted in
        the compaction, i.e. the type environment is a clean slate.  For this
        reason, it is suitable only for let-bound contexts."""
        history_env = self.get_type_env()
        if len(history_env.type_var_set) == 0:
            return self
        c = self.copy()
        # note: the following is already triggered by copy.  If this behavior
        # changes, this needs updating.
        env = c.get_type_env()
        if len(env.type_var_set) == 0:
            return c
        if used_vars_only:
            tenv = env.type_var_set - set(env.type_mapping.keys())
        else:
            tenv = env.type_var_set
        if len(tenv) == 0:
            return self
        compacted_map = types.compact_type_set(tenv, unsafe=unsafe)
        result = self.under_type_injection(compacted_map)
        result._type_env_history = history_env
        if not store_mapping:
            result.get_type_env(force_recalc=True)
        return result


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
        return variable_replace_unify(self, a2)

    # the next sequence of functions is clearly inefficient, and could be
    # replaced by memoization (e.g. 'director strings' or whatever). But I
    # don't think it matters for this application.
    def free_variables(self):
        """Find the set of variables that are free in the typed expression.
        """
        result = set()
        if len(self.args) == 0:
            if is_var_symbol(self.op):
                # should not be reachable
                assert False
                result = {self.op}

        if isinstance(self.op, TypedExpr):
            result.update(self.op.free_variables())
        for a in self.args:
            if isinstance(a, TypedExpr):
                result.update(a.free_variables())
            elif is_var_symbol(a):
                result.add(a)
        return result

    def bound_variables(self):
        """Find the set of variables that are bound (somewhere) in a typed
        expression.

        Note that this may be overlapping with the set of free variables.
        """
        result = set()
        for a in self.args:
            result.update(a.bound_variables())
        return result

    def find_safe_variable(self, starting="x"):
        """Find an a safe alpha variant of the starting point (by default: 'x'),
        that is not used in the expression."""
        blockset = self.free_variables() | self.bound_variables()
        varname = alpha_variant(starting, blockset)
        return varname

    def term(self):
        return (isinstance(self.op, str) and len(self.args) == 0)

    def functional(self):
        funtype = unify(self.type, tp("<X,Y>"))
        return (funtype is not None)

    def atomic(self):
        return len(self.args) == 0

    def simplify(self):
        return self

    def simplify_all(self):
        result = self
        dirty = False
        for i in range(len(result.args)):
            new_arg_i = result.args[i].simplify_all()
            if new_arg_i is not result.args[i]:
                dirty = True
                result = derived(result.subst(i, new_arg_i), result,
                    desc=("Recursive simplification of argument %i"
                            % i),
                    subexpression=new_arg_i)
        result = result.simplify()
        return result

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
        condition = true_term
        new_parts = list()
        for part in self:
            part_i = part.calculate_partiality(vars=vars)
            if isinstance(part_i, Partial):
                condition = condition & part_i.condition
                part_i = part_i.body
            new_parts.append(part_i)
        new_self = self.copy_local(*new_parts)
        condition = condition.simplify_all()
        if condition is true_term:
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
        
        #print("globals: ", globals())
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

    def latex_str(self, **kwargs):
        """Return a representation of the TypedExpr suitable for Jupyter
        Notebook display.

        In this case the output should be pure LaTeX."""
        assert not isinstance(self.op, TypedExpr)
        if not self.args:
            return ensuremath(str(self.op))
        # past this point in the list of cases should only get hard-coded
        # operators
        elif len(self.args) == 1: # Prefix operator
            return ensuremath(text_op_in_latex(self.op)
                                        + self.args[0].latex_str(**kwargs))
        else:                     # Infix operator
            return ensuremath('(%s)' %
                (' '+text_op_in_latex(self.op)+' ').join(
                                    [a.latex_str(**kwargs) for a in self.args]))

    def _repr_latex_(self):
        return self.latex_str()

    def __str__(self):
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
    def __mod__(self, other):    return self.factory('<=>',  self, other)

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
    def __pow__(self, other):    return self.factory('**', self, other)

    def __bool__(self):
        # otherwise, python tries to use the fact that these objects implement a
        # container interface to convert to bool, which can lead to weird
        # results.
        # TODO: revisit... (see also false_term)
        return True


TypedExpr.add_local('TypedExpr', TypedExpr)

class ApplicationExpr(TypedExpr):
    def __init__(self, fun, arg, defer=False, assignment=None, type_check=True):
        if type_check and not defer:
            tc_result = self.fa_type_inference(fun, arg, assignment)
            if tc_result is None:
                if not fun.functional():
                    raise TypeMismatch(fun, arg, "Function-argument expression: left subexpression is not a function")
                else:
                    raise TypeMismatch(fun, arg, "Function-argument expression: mismatched types")
            fun, arg, out_type, history = tc_result
            op = "Apply"
            args = [fun, arg]
            self.type = out_type
        else:
            history = False
            op = "Apply"
            args = [fun, arg]
            # note: fun.type MUST be functional!
            self.type = fun.type.right
        super().__init__(op, *args, defer=defer)
        if fun.let and arg.let:
            self.let = True

        if history:
            # bit of a hack: build a derivation with the deferred version as
            # the origin
            old = ApplicationExpr(fun, arg, defer=True)
            derived(self, old, desc="Type inference")    
        if isinstance(fun, LFun):
            arg.type_not_guessed()
        else:
            # not 100% that the following is the right fix...
            try:
                self.type_guessed = fun.type_guessed
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

    def latex_str(self, **kwargs):
        fun = self.args[0]
        arg = self.args[1]
        if isinstance(arg, Tuple):
            arg_str = arg.latex_str(**kwargs) # tuple already generates parens
        else:
            arg_str = "(%s)" % (arg.latex_str(**kwargs))
        if isinstance(fun, CustomTerm):
            return ensuremath(fun.custom_appl_latex(arg_str))
        elif isinstance(fun, LFun):
            return ensuremath("{[%s]}%s" % (fun.latex_str(**kwargs), arg_str))
        else:
            return ensuremath('%s%s' % (fun.latex_str(**kwargs), arg_str))

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
        ts = get_type_system()
        old_fun = None
        old_arg = None
        if fun.let:
            fun = fun.freshen_type_vars()
        if arg.let:
            arg = arg.freshen_type_vars()
        history = False
        (f_type, a_type, out_type) = ts.unify_fa(fun.type, arg.type)
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

        return (fun, arg, out_type, history)

    def reducible(self):
        if isinstance(self.args[0], LFun) or isinstance(self.args[0],
                                                                Disjunctive):
            return True
        return False

    def reduce(self):
        """if there are arguments to op, see if a single reduction is
        possible."""
        if not self.reducible():
            return self
        else:
            return derived(self.args[0].apply(self.args[1]), self,
                                                            desc="Reduction")

    def calculate_partiality(self, vars=None):
        # defer calculation of the argument until beta reduction has occurred
        if isinstance(self.args[0], LFun):
            return self
        else:
            return super().calculate_partiality()

    @classmethod
    def random(self, random_ctrl_fun):
        ftyp = get_type_system().random_from_class(types.FunType)
        fun = random_lfun_force_bound(ftyp, random_ctrl_fun)
        arg = random_ctrl_fun(typ=ftyp.left)
        return ApplicationExpr(fun, arg)


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

    def latex_str(self, parens=True, **kwargs):
        inner = ", ".join([a.latex_str(**kwargs) for a in self.args])
        if parens:
            return ensuremath("(" + inner + ")")
        else:
            return ensuremath(inner)

    @classmethod
    def random(cls, ctrl, max_type_depth=1, max_tuple_len=5, allow_empty=True):
        if allow_empty:
            r = range(max_tuple_len+1)
        else:
            r = range(max_tuple_len+1)[1:]
        length = random.choice(r)
        signature = [get_type_system().random_type(max_type_depth, 0.5)
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
        if isinstance(self.op, Number): # this isn't very elegant...
            if self.type != type_n:
                raise TypeMismatch(self.op, self.type,
                                                "Numeric must have type n")
            self.type_guessed = False
            self.suppress_type = True # suppress types for numbers
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

    def free_variables(self):
        if is_var_symbol(self.op):
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
        if suppress_constant_type and self.constant():
            return False
        if suppress_constant_predicate_type:
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

    def _repr_latex_(self):
        return self.latex_str()

    random_term_base = {type_t : "p", type_e : "x", type_n : "n"}

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
            if typ in random_term_base.keys():
                base = random_term_base[typ]
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

    def latex_str_long(self):
        return latex_str(self)

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def from_op(cls, op):
        return MiniOp(op.op_name, op.op_name_latex)

###############
#
# Partiality
#
###############

class Partial(TypedExpr):
    def __init__(self, body, condition, type_check=True):
        if condition is None:
            condition = true_term
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
        
    def latex_str(self, **kwargs):
        if self.condition and self.condition != true_term:
            return ensuremath("\\left|\\begin{array}{l}%s\\\\%s\\end{array}\\right|"
                % (self.body.latex_str(**kwargs),
                   self.condition.latex_str(**kwargs)))
        else:
            return ensuremath("%s" % (self.body.latex_str(**kwargs)))

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
            return true_term
        
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
                            " (type %s appears duplicated in expression '%s' "
                            "for disjuncts '%s')"
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
    
    def latex_str(self, disj_type=False, **kwargs):
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
            raise TypeMismatch(self,arg, "Application to a non-functional Disjunction")
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
            raise TypeMismatch(self,arg, "Application to a non-functional Disjunction")
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



class UnaryOpExpr(TypedExpr):
    """This class abstracts over expressions headed by specific unary operators.
    It is not necessarily designed to be instantiated directly, but rather
    subclassed for particular hard-coded operators.

    Because of the way the copy function works, it is currently not suited for
    direct instantiation.

    In logical terms, this corresponds to syncategorematic definitions of
    operators as is standard in definitions of logics. For example, statements
    like '~p is a sentence iff p is a sentence'.  While semantics is not
    currently implemented, it could be done in subclasses."""
    def __init__(self, typ, op, arg1, op_name_uni=None, op_name_latex=None,
                                                            tcheck_args=True):
        if tcheck_args:
            super().__init__(op, self.ensure_typed_expr(arg1, typ))
        else:
            super().__init__(op, self.ensure_typed_expr(arg1))

        self.type = typ
        if op_name_uni is None:
            self.op_name = op
        else:
            self.op_name = op_name_uni
        if op_name_latex is None:
            self.op_name_latex = self.op_name
        else:
            self.op_name_latex = op_name_latex
        self.operator_style = True

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, type_check=True):
        """This must be overriden in classes that are not produced by the
        factory."""
        return op_expr_factory(self.op, *args)

    def __str__(self):
        return "%s%s\nType: %s" % (self.op_name, repr(self.args[0]), self.type)

    def __repr__(self):
        if (self.operator_style):
            return "%s%s" % (self.op_name, repr(self.args[0]))
        else:
            return "%s(%s)" % (self.op_name, repr(self.args[0]))

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self, **kwargs):
        if (self.operator_style):
            return ensuremath("%s %s" % (self.op_name_latex,
                                            self.args[0].latex_str(**kwargs)))
        else:
            return ensuremath("%s(%s)" % (self.op_name_latex,
                                            self.args[0].latex_str(**kwargs)))


    @classmethod
    def random(cls, ctrl):
        return cls(ctrl(typ=type_t))


class BinaryOpExpr(TypedExpr):
    """This class abstracts over expressions headed by specific binary
    operators.  It is not necessarily designed to be instantiated directly, but
    rather subclassed for particular hard-coded operators.

    Because of the way the copy function works, it is currently not suited for
    direct instantiation at all."""
    def __init__(self, typ, op, arg1, arg2, op_name_uni=None,
                                    op_name_latex=None, tcheck_args=True):
        if tcheck_args:
            args = [self.ensure_typed_expr(arg1, typ),
                    self.ensure_typed_expr(arg2, typ)]
        else:
            args = [self.ensure_typed_expr(arg1), self.ensure_typed_expr(arg2)]
        super().__init__(op, *args)
        self.type = typ
        if op_name_uni is None:
            self.op_name = op
        else:
            self.op_name = op_name_uni
        if op_name_latex is None:
            self.op_name_latex = self.op_name
        else:
            self.op_name_latex = op_name_latex

    def copy(self):
        return self.copy_local(*self.args)

    def copy_local(self, *args, type_check=True):
        """This must be overriden by classes that are not produced by the
        factory."""
        return op_expr_factory(self.op, *args)

    def __str__(self):
        return "%s\nType: %s" % (repr(self), self.type)

    def __repr__(self):
        return "(%s %s %s)" % (repr(self.args[0]), self.op_name,
                                                        repr(self.args[1]))

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self, **kwargs):
        return ensuremath("(%s %s %s)" % (self.args[0].latex_str(**kwargs), 
                                          self.op_name_latex,  
                                          self.args[1].latex_str(**kwargs)))

    @classmethod
    def join(cls, *l):
        """Joins an arbitrary number of arguments using the binary operator.
        Note that currently association is left to right. Requires a subclass
        that defines a two-parameter __init__ function.  (I.e. will potentially
        fail if called on the abstract class.)

        Will also fail on operators that do not take the same type (i.e.
        SetContains).
        """
        if len(l) == 0:
            return true_term
        if len(l) == 1:
            return l[0]
        else:
            cur = l[0]
            for i in range(len(l) - 1):
                cur = cls(cur, l[i+1]) # will raise an error if the subclass
                                       # doesn't define a constructor this way.
            return cur

    @classmethod
    def random(cls, ctrl):
        return cls(ctrl(typ=type_t), ctrl(typ=type_t))


# could make a factory function for these

class UnaryNegExpr(UnaryOpExpr): #unicode: ¬
    def __init__(self, body):
        super().__init__(type_t, "~", body, "~", "\\neg{}")

    def simplify(self):
        if self.args[0] == true_term:
            return derived(false_term, self, desc="negation")
        elif self.args[0] == false_term:
            return derived(true_term, self, desc="negation")
        else:
            return self


class BinaryAndExpr(BinaryOpExpr): #note: there is a unicode, ∧.
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "&", arg1, arg2, "&", "\\wedge{}")

    def simplify(self):
        if self.args[0] == false_term or self.args[1] == false_term:
            return derived(false_term, self, desc="conjunction")
        elif self.args[0] == true_term:
            return derived(self.args[1].copy(), self, desc="conjunction")
        elif self.args[1] == true_term:
            return derived(self.args[0].copy(), self, desc="conjunction")
        elif self.args[0] == self.args[1]:
            return derived(self.args[0].copy(), self, desc="conjunction")
        else:
            return self

class BinaryOrExpr(BinaryOpExpr): #unicode: ∨.
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "|", arg1, arg2, "|", "\\vee{}")

    def simplify(self):
        if self.args[0] == true_term or self.args[1] == true_term:
            return derived(true_term, self, desc="disjunction")
        elif self.args[0] == false_term:
            # covers case of False | False
            return derived(self.args[1].copy(), self, desc="disjunction")
        elif self.args[1] == false_term:
            return derived(self.args[0].copy(), self, desc="disjunction")            
        elif self.args[0] == self.args[1]:
            return derived(true_term, self, desc="disjunction")
        else:
            return self


#unicode arrow: →
class BinaryArrowExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, ">>", arg1, arg2, ">>", "\\rightarrow{}")

    def simplify(self):
        if self.args[0] == false_term:
            return derived(true_term, self, desc="material implication")
        elif self.args[0] == true_term:
            return derived(self.args[1].copy(), self,
                                                desc="material implication")
        elif self.args[1] == false_term:
            return derived(UnaryNegExpr(self.args[0]), self,
                                                desc="material implication")
        elif self.args[1] == true_term:
            return derived(true_term, self, desc="material implication")
        elif self.args[0] == self.args[1]:
            return derived(true_term, self, desc="material implication")
        else:
            return self

# unicode: ↔
class BinaryBiarrowExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "<=>", arg1, arg2, "<=>", "\\leftrightarrow{}")

    def simplify(self):
        if self.args[0] == false_term:
            if self.args[1] == true_term:
                return derived(false_term, self, desc="biconditional")
            elif self.args[1] == false_term:
                return derived(true_term, self, desc="biconditional")
            else:
                return derived(UnaryNegExpr(self.args[1]), self,
                                                            "biconditional")
        elif self.args[0] == true_term:
            if self.args[1] == false_term:
                return derived(false_term, self, desc="biconditional")
            elif self.args[1] == true_term:
                return derived(true_term, self, desc="biconditional")
            else:
                return derived(self.args[1].copy(), self, desc="biconditional")
        elif self.args[1] == false_term: # term+term is already taken care of
            return derived(UnaryNegExpr(self.args[0]), self,
                                                        desc="biconditional")
        elif self.args[1] == true_term:
            return derived(self.args[0].copy(), self, desc="biconditional")
        elif self.args[0] == self.args[1]:
            return derived(true_term, self, desc="biconditional")
        else:
            return self


# TODO: generalize this?
class BinaryNeqExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "^", arg1, arg2, "=/=", "\\not=")

    def simplify(self):
        if self.args[0] == false_term:
            if self.args[1] == true_term:
                return derived(true_term, self, desc="neq")
            elif self.args[1] == false_term:
                return derived(false_term, self, desc="neq")
            else:
                return derived(self.args[1].copy(), self, desc="neq")
                
        elif self.args[0] == true_term:
            if self.args[1] == false_term:
                return derived(true_term, self, desc="neq")
            elif self.args[1] == true_term:
                return derived(false_term, self, desc="neq")
            else:
                return derived(UnaryNegExpr(self.args[1]), self, desc="neq")
        elif self.args[1] == true_term: # term+term is already taken care of
            return derived(UnaryNegExpr(self.args[0]), self, desc="neq")
        elif self.args[1] == false_term:
            return derived(self.args[0].copy(), self, desc="neq")
        elif self.args[0] == self.args[1]:
            return derived(false_term, self, desc="neq")
        else:
            # note: don't simplify p =/= q; this would be a job for a prover
            return self




class BinaryGenericEqExpr(BinaryOpExpr):
    """Type-generic equality.  This places no constraints on the type of `arg1`
    and `arg2` save that they be equal.  See `eq_factory`."""
    def __init__(self, arg1, arg2):
        arg1 = self.ensure_typed_expr(arg1)
        # maybe raise the exception directly?
        arg2 = self.ensure_typed_expr(arg2, arg1.type)
        # some problems with equality using '==', TODO recheck, but for now
        # just use "<=>" in the normalized form
        super().__init__(type_t, "<=>", arg1, arg2, op_name_uni = "<=>",
                                op_name_latex = "=", tcheck_args = False)

    def simplify(self):
        if self.args[0] == self.args[1]:
            return derived(true_term, self, desc="Equality")
        else:
            if (isinstance(self.args[0].op, Number)
                                and isinstance(self.args[1].op, Number)):
                return derived(false_term, self, desc="Equality")
            else:
                return self # this would require a solver for the general case

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        body_type = get_type_system().random_type(max_type_depth, 0.5)
        return cls(ctrl(typ=body_type), ctrl(typ=body_type))


def eq_factory(arg1, arg2):
    """If type is type t, return a biconditional.  Otherwise, build an equality
    statement."""
    arg1 = TypedExpr.ensure_typed_expr(arg1)
    arg2 = TypedExpr.ensure_typed_expr(arg2)
    ts = get_type_system()
    if arg1.type == types.type_t: # this must be exact so as not to trigger on
                                  # combinators.  TODO: something more general?
        return BinaryBiarrowExpr(arg1, arg2)
    else:
        return BinaryGenericEqExpr(arg1, arg2)


def binary_num_op(op, op_uni=None, op_latex=None, simplify_fun=None):
    """Factory for binary numeric operators."""
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            super().__init__(type_n, op, arg1, arg2, op_uni, op_latex)

        def simplify(self):
            if simplify_fun is None:
                return self
            if (isinstance(self.args[0].op, Number)
                                    and isinstance(self.args[1].op, Number)):
                return derived(te(simplify_fun(self.args[0].op,
                                               self.args[1].op)),
                                    self, desc=op_uni)
            else:
                return self

        @classmethod
        def random(cls, ctrl):
            return cls(ctrl(typ=type_n), ctrl(typ=type_n))

    return BinOp

def binary_num_rel(op, op_uni=None, op_latex=None, simplify_fun=None):
    """Factory for binary numeric relations."""
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            # this is a bit redundant but it works
            super().__init__(type_t, op,
                    self.ensure_typed_expr(arg1, types.type_n),
                    self.ensure_typed_expr(arg2, types.type_n),
                    op_uni, op_latex, tcheck_args=False)

        def simplify(self):
            if simplify_fun is None:
                return self
            if (isinstance(self.args[0].op, Number)
                                    and isinstance(self.args[1].op, Number)):
                return derived(te(simplify_fun(self.args[0].op,
                                               self.args[1].op)),
                                self, desc=op_uni)
            else:
                return self

        @classmethod
        def random(cls, ctrl):
            return cls(ctrl(typ=type_n), ctrl(typ=type_n))

    return BinOp

BinaryLExpr = binary_num_rel("<", "<", "<", simplify_fun=lambda x,y: x<y)
BinaryLeqExpr = binary_num_rel("<=", "<=", "\\leq{}",
                                            simplify_fun=lambda x,y: x<=y)
BinaryGeqExpr = binary_num_rel(">=", ">=", "\\geq{}",
                                            simplify_fun=lambda x,y: x>=y)
BinaryGExpr = binary_num_rel(">", ">", ">", simplify_fun=lambda x,y: x>y)
BinaryPlusExpr = binary_num_op("+", "+", "+", simplify_fun=lambda x,y: x+y)
BinaryMinusExpr = binary_num_op("-", "-", "-", simplify_fun=lambda x,y: x-y)
BinaryDivExpr = binary_num_op("/", "/", "/", simplify_fun=lambda x,y: x/y)
BinaryTimesExpr = binary_num_op("*", "*", "*", simplify_fun=lambda x,y: x*y)
BinaryExpExpr = binary_num_op("**", "**", "**", simplify_fun=lambda x,y: x**y)


# There's only one of these, so a factory would be silly
class UnaryNegativeExpr(UnaryOpExpr):
    def __init__(self, body):
        super().__init__(type_n, "-", body, "-", "-")

    def simplify(self):
        if isinstance(self.args[0].op, Number):
            return derived(te(- self.args[0].op), self, desc="unary -")
        else:
            return self

    @classmethod
    def random(cls, ctrl):
        return cls(ctrl(typ=type_n))


class SetContains(BinaryOpExpr):
    """Binary relation of set membership.  This uses `<<` as the symbol.

    Note that this _does_ support reduction if the set describes its members by
    condition, as set membership is equivalent to saturation of the
    characteristic function of the set."""
    def __init__(self, arg1, arg2, type_check=True):
        # seems like the best way to do the mutual type checking here?
        # Something more elegant?
        arg1 = self.ensure_typed_expr(arg1)
        arg2 = self.ensure_typed_expr(arg2, types.SetType(arg1.type))
        arg1 = self.ensure_typed_expr(arg1, arg2.type.content_type)
        #super().__init__(type_t, "<<", arg1, arg2, "∈", "\\in{}", tcheck_args=False)
        # was having some trouble with the ∈ symbol, not sure what the problem is but disabled for now.
        super().__init__(type_t, "<<", arg1, arg2, "<<", "\\in{}",
                                                    tcheck_args=False)

    def copy(self):
        return SetContains(self.args[0], self.args[1])

    def copy_local(self, arg1, arg2, type_check=True):
        return SetContains(arg1, arg2)

    def reduce(self):
        if isinstance(self.args[1], ConditionSet):
            derivation = self.derivation
            step = (self.args[1].to_characteristic()(self.args[0])).reduce()
            step.derivation = derivation # suppress the intermediate parts of
                                         # this derivation, if any
            return derived(step, self, "∈ reduction")
        else:
            # leave ListedSets as-is for now.  TODO could expand this using
            # disjunction.
            return self

    def reducible(self):
        if isinstance(self.args[1], ConditionSet):
            return True
        return False

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        content_type = get_type_system().random_type(max_type_depth, 0.5)
        return SetContains(ctrl(typ=content_type), ctrl(
                                            typ=types.SetType(content_type)))


class TupleIndex(BinaryOpExpr):
    def __init__(self, arg1, arg2, type_check=True):
        arg1 = self.ensure_typed_expr(arg1)
        if not isinstance(arg1.type, types.TupleType):
            raise types.TypeMismatch(arg1, arg2,
                    mode="Tuple indexing expression with a non-tuple")
        arg2 = self.ensure_typed_expr(arg2, types.type_n)
        if isinstance(arg2.op, Number): # TODO better way to determine whether
                                        # arg2 is a constant of type type_n?
            if arg2.op >= len(arg1.type):
                raise TypeMismatch(arg1, arg2,
                    mode="Tuple indexing expression with out-of-range index")
            output_type = arg1.type[arg2.op]
        else:
            output_type = types.VariableType("X") # TODO this is problematic
            logger.warning(
                "Using non-constant tuple index; not well-supported.")
        super().__init__(output_type, "[]", arg1, arg2, "[]", "[]",
                                                            tcheck_args=False)

    def copy(self):
        return TupleIndex(self.args[0], self.args[1])

    def copy_local(self, arg1, arg2, type_check=True):
        return TupleIndex(arg1, arg2)

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        if isinstance(self.args[1].op, Number):
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

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self, **kwargs):
        return ensuremath("(%s[%s])" % (self.args[0].latex_str(**kwargs),
                                        self.args[1].latex_str(**kwargs)))

    def reduce(self):
        if (isinstance(self.args[0], Tuple)
                                    and isinstance(self.args[1].op, Number)):
            result = self.args[0].tuple()[self.args[1].op].copy()
            return derived(result, self, "Resolution of index")
        else:
            return self


    def reducible(self):
        if (isinstance(self.args[0], Tuple)
                                    and isinstance(self.args[1].op, Number)):
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


unary_symbols_to_op_exprs = {"~" : UnaryNegExpr,
                        "-" : UnaryNegativeExpr}

# not implemented: << as left implication.  I am using << for set membership.
# note that neq is for type t only.
binary_symbols_to_op_exprs = {
                        "&" : BinaryAndExpr,
                        "|" : BinaryOrExpr,
                        ">>" : BinaryArrowExpr,
                        "<=>" : eq_factory,
                        "==" : eq_factory,
                        "%" : BinaryNeqExpr,
                        "^" : BinaryNeqExpr,
                        "<" : BinaryLExpr,
                        ">" : BinaryGExpr,
                        "<=" : BinaryLeqExpr,
                        ">=" : BinaryGeqExpr,
                        "+" : BinaryPlusExpr,
                        "-" : BinaryMinusExpr,
                        "/" : BinaryDivExpr,
                        "*" : BinaryTimesExpr,
                        "**" : BinaryExpExpr,
                        "<<" : SetContains}

op_symbols = (set(unary_symbols_to_op_exprs.keys())
                | set(binary_symbols_to_op_exprs.keys()))



# TODO raise exceptions
def op_expr_factory(op, *args):
    """Given some operator/relation symbol with arguments, construct an
    appropriate TypedExpr subclass for that operator."""

    # this conditional is necessary because the same symbol may involve both a
    # unary and a binary operator
    if len(args) == 0:
        raise ValueError("0-length operator")
    elif len(args) == 1:
        if op not in unary_symbols_to_op_exprs:
            raise ValueError("Unknown unary operator symbol '%s'" % op)
        else:
            return unary_symbols_to_op_exprs[op](args[0])
    elif len(args) == 2:
        if op not in binary_symbols_to_op_exprs:
            raise ValueError("Unknown binary operator symbol '%s'" % op)
        else:
            return binary_symbols_to_op_exprs[op](args[0], args[1])
    else:
        raise ValueError("Too many arguments (%s) to operator '%s'"
                                                        % (len(args), op))



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

    binding_operators = dict()
    canonicalize_names = dict()
    unparsed_operators = set()
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

    @classmethod
    def binding_op_factory(self, op_class, var_list, body, assignment=None):
        for i in range(len(var_list)):
            if not is_var_symbol(var_list[i][0]):
                raise parsing.ParseError(
                    "Need variable name in binding operator expression"
                    " (received '%s')" % var_list[i][0], None)
            if var_list[i][1] is None:
                # TODO: flag as a guessed type somehow?
                var_list[i] = (var_list[i][0],
                                default_variable_type(var_list[i][0]))
        if op_class.allow_multivars or op_class.allow_novars:
            # use alternate constructor
            if (not op_class.allow_multivars) and len(var_list) > 1:
                raise parsing.ParseError(
                    "Operator class '%s' does not allow >1 variables"
                    % (op_class.canonical_name), None)                
            if (not op_class.allow_novars) and len(var_list) == 0:
                raise parsing.ParseError(
                    "Operator class '%s' does not allow 0 variables"
                    % (op_class.canonical_name), None)                
            return op_class(var_list, body, assignment=assignment)
        else:
            if len(var_list) != 1:
                raise parsing.ParseError(
                    "Operator class '%s' does not allow %i variables"
                    % (op_class.canonical_name, len(var_list)), None)
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
        if isinstance(var_or_vtype, str): # TODO: support type strings
            var_or_vtype = TypedExpr.term_factory(var_or_vtype)
        if isinstance(var_or_vtype, TypedTerm):
            if varname is not None:
                logger.warning("Overriding varname '%s' with '%s'"
                                            % (varname, var_or_vtype.op))
            varname = var_or_vtype.op
            vartype = var_or_vtype.type
        elif isinstance(var_or_vtype, types.TypeConstructor):
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
            self.init_body(self.ensure_typed_expr(body, body_type,
                                                        assignment=sassign))
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
    def add_op(cls, op):
        """Register an operator to be parsed."""
        if op.canonical_name is None:
            BindingOp.unparsed_operators.add(op)
        else:
            if op.canonical_name in BindingOp.binding_operators:
                logger.warning(
                    "Overriding existing binding operator '%s' in registry"
                    % op.canonical_name)
                cls.remove_op(op)
            BindingOp.binding_operators[op.canonical_name] = op
            for alias in op.secondary_names:
                BindingOp.canonicalize_names[alias] = op.canonical_name
        BindingOp.compile_ops_re()

    @classmethod
    def remove_op(cls, op):
        """Remove an operator from the parsing registry."""
        for alias in BindingOp.binding_operators[op.canonical_name].secondary_names:
            del BindingOp.canonicalize_names[alias]
        if op.canonical_name is None:
            BindigOp.unparsed_operators.remove(op)
        else:
            del BindingOp.binding_operators[op.canonical_name]
        BindingOp.compile_ops_re()

    @classmethod
    def compile_ops_re(cls):
        """Recompile the regex for detecting operators."""
        op_names = (BindingOp.binding_operators.keys()
                                            | BindingOp.canonicalize_names)
        # sort with longer strings first, to avoid matching subsets of long
        # names i.e. | is not greedy, need to work around that.
        op_names = list(op_names)
        op_names.sort(reverse=True)
        if len(op_names) == 0:
            BindingOp.op_regex = None
            BindingOp.init_op_regex = None
        else:
            regex = "(" + ("|".join(op_names)) + ")"
            BindingOp.op_regex = re.compile(regex)
            BindingOp.init_op_regex = re.compile(r'^\s*' + regex)

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

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self, assignment=None, **kwargs):
        assignment = self.scope_assignment(assignment=assignment)
        return ensuremath("%s %s" % (self.latex_op_str(),  
                        self.body.latex_str(assignment=assignment, **kwargs)))

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


    def free_variables(self):
        return super().free_variables() - {self.varname}

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
        b_cls = type(b)
        if isinstance(b, ConditionSet) or isinstance(b, LFun):
            return b
        else: # IotaPartial handled in subclass
            return Partial(b_cls(b.var_instance, body),
                                            ForallUnary(b.var_instance, body))

    def project_partiality_weak(b, body, condition):
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
                    "No implemented way of projecting partiality for BindingOp %s"
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
            if new_body.condition is true_term:
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

        i = 0
        if BindingOp.init_op_regex is None:
            return None # no operators to parse
        op_match = re.match(BindingOp.init_op_regex, s)
        if not op_match:
            raise parsing.ParseError(
                "Unknown operator when trying to parsing "
                "binding operator expression", s, None, met_preconditions=False)
        op_name = op_match.group(1) # operator name
        i = op_match.end(1)

        if op_name in BindingOp.canonicalize_names:
            op_name = BindingOp.canonicalize_names[op_name]
        if op_name not in BindingOp.binding_operators:
            raise Error(
                "Can't find binding operator '%s'; should be impossible"
                % op_name)
        op_class = BindingOp.binding_operators[op_name]

        split = s.split(":", 1)
        if (len(split) != 2):
            # possibly should change to met_preconditions = True in the future.
            # At this point, we have seen a binding expression token.
            raise parsing.ParseError(
                "Missing ':' in binding operator expression", s, None,
                met_preconditions=False)
        header, remainder = split
        vname = header[i:].strip() # removes everything but a variable name
        var_seq = cls.try_parse_term_sequence(vname, lower_bound=None,
                                    upper_bound=None, assignment=assignment)
        return (op_class, var_seq, remainder)

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
        try:
            body = TypedExpr.try_parse_paren_struc_r(new_struc,
                        assignment=assignment, locals=locals, vprefix=vprefix)
        except Exception as e:
            if isinstance(e, parsing.ParseError):
                raise e
            else:
                raise parsing.ParseError(
                    "Binding operator expression has unparsable body",
                    parsing.flatten_paren_struc(struc), None, e=e)
        if body is None:
            raise parsing.ParseError(
                "Can't create body-less binding operator expression",
                parsing.flatten_paren_struc(struc), None)
        result = BindingOp.binding_op_factory(op_class, var_list, body,
            assignment=assignment)
        return result

    @classmethod
    def random(cls, ctrl, body_type=type_t, max_type_depth=1):
        global random_used_vars
        var_type = get_type_system().random_type(max_type_depth, 0.5)
        variable = random_term(var_type, usedset=random_used_vars,
                                                prob_used=0.2, prob_var=1.0)
        random_used_vars |= {variable}
        return cls(variable, ctrl(typ=type_t))


class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""

    canonical_name = "Set"
    op_name_uni="Set"
    op_name_latex="Set"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body,
                varname=varname, body_type=types.type_t, assignment=assignment,
                type_check=type_check)
        self.type = types.SetType(self.vartype)

    def structural_singleton(self):
        pass

    def term(self):
        return False

    def latex_str(self, parens=True, **kwargs):
        return ensuremath("\\{%s_{%s}\\:|\\: "
                            % (self.varname, self.vartype.latex_str())
                    + self.body.latex_str(**kwargs) + "\\}")

    def __lshift__(self, i):
        return SetContains(i, self)

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname)

    def try_adjust_type_local(self, unified_type, derivation_reason,
                                                            assignment, env):
        inner_type = unified_type.content_type
        char = self.to_characteristic()
        sub_var = TypedTerm(self.varname, inner_type)
        new_condition = char.apply(sub_var)
        return self.copy_local(sub_var, new_condition)

BindingOp.add_op(ConditionSet)

class ListedSet(TypedExpr):
    """A listed set is a set that simply lists members."""
    canonical_name = "ListedSet"
    op_name_uni="ListedSet"
    op_name_latex="ListedSet"

    def __init__(self, iterable, typ=None, assignment=None, type_check=True):
        s = set(iterable) # remove duplicates, flatten order
        args = [self.ensure_typed_expr(a,assignment=assignment) for a in s]
        args = sorted(args, key=repr) # for a canonical ordering
        if len(args) == 0 and typ is None:
            typ = types.VariableType("X") # could be a set of anything
        elif typ is None:
            typ = args[0].type
        for i in range(len(args)):
            # type checking TODO: this isn't right, would need to pick the
            # strongest type
            args[i] = self.ensure_typed_expr(args[i], typ)
        super().__init__("Set", *args)
        #self.op = "Set"
        self.type = types.SetType(typ)

    def subst(self, i, s):
        if len(self.args) < 2:
            return super().subst(i, s)
        else:
            raise NotImplementedError(
                "Beta reduction into a set of size>1 not currently supported.")
            # TODO deal with this
            # the problem is the same as usual -- set order isn't stable so we
            # need to do this all at once rather than  member-by-member.

    def copy(self):
        return ListedSet(self.args)

    def copy_local(self, *args, type_check=True):
        return ListedSet(args)

    def term(self):
        return False

    def __lshift__(self, i):
        """Use the `<<` operator for set membership."""
        return SetContains(i, self)

    def set(self):
        """Return a python `set` version of the ListedSet.

        Note that this isn't guaranteed to be defined for anything with a set
        type."""
        return set(self.args)

    def cardinality(self):
        return len(self.args)

    def to_condition_set(self):
        """Convert to a condition set by disjoining members."""
        # ensure that we build a condition set from a variable that is not free
        # in any of the members
        varname = self.find_safe_variable(starting="x")
        conditions = [BinaryGenericEqExpr(TypedTerm(varname, a.type), a)
                                                            for a in self.args]
        return ConditionSet(self.type.content_type,
                            BinaryOrExpr.join(*conditions), varname=varname)

    def reduce_all(self):
        """Special-cased reduce_all for listed sets.  There are two problems.
        First, the reduction may actually result in a change in the size of the
        set, something generally not true of reduction elsewhere.  Second,
        because the constructor calls `set`, `copy` is not guaranteed to return
        an object with a stable order.  Therefore we must batch the reductions
        (where the TypedExpr version doesn't).

        Note that currently this produces non-ideal derivation sequences."""
        dirty = False
        accum = list()
        result = self
        for i in range(len(result.args)):
            new_arg_i = result.args[i].reduce_all()
            if new_arg_i is not result.args[i]:
                dirty = True
                reason = "Recursive reduction of set member %s" % (i+1)
                # TODO: this isn't quite right but I can't see what else to do
                # right now
                result = derived(result, result, desc=reason,
                                    subexpression=new_arg_i, allow_trivial=True)
                accum.append(new_arg_i)
            else:
                accum.append(new_arg_i)
        if dirty:
            new_result = ListedSet(accum)
            new_result = derived(new_result, result,
                            desc="Construction of set from reduced set members")
            result = new_result
        return result


    def __repr__(self):
        return repr(set(self.args))

    def latex_str(self, **kwargs):
        inner = ", ".join([a.latex_str(**kwargs) for a in self.args])
        return ensuremath("\\{" + inner + "\\}")

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        inner_type = unified_type.content_type
        content = [a.try_adjust_type(inner_type,
                        derivation_reason=derivation_reason,
                        assignment=assignment) for a in self.args]
        result = self.copy_local(*content)
        return result

    @classmethod
    def random(self, ctrl, max_type_depth=1, max_members=6, allow_empty=True):
        typ = get_type_system().random_type(max_type_depth, 0.5)
        if allow_empty:
            r = range(max_members+1)
        else:
            r = range(max_members+1)[1:]
        length = random.choice(r)
        members = [ctrl(typ=typ) for i in range(length)]
        return ListedSet(members)



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
        # (would return True)
        if not self.varname in self.body.free_variables():
            return self.body
        return self

BindingOp.add_op(ForallUnary)

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

BindingOp.add_op(ExistsUnary)

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

BindingOp.add_op(ExistsExact)

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

BindingOp.add_op(IotaUnary)
BindingOp.add_op(IotaPartial)

class LFun(BindingOp):
    """A typed function.  Can itself be used as an operator in a TypedExpr.

    """
    canonical_name = "Lambda"
    secondary_names = {"L", "λ", "lambda"}
    op_name_uni="λ"
    op_name_latex="\\lambda{}"

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
            raise TypeMismatch(self,arg, "Application")

    def compose(self, other):
        """Function composition."""
        return fun_compose(self, other)

    def __mul__(self, other):
        """Override `*` as function composition for LFuns.  Note that this
        _only_ works for LFuns currently, not functional constants/variables."""
        return self.compose(other)

    @classmethod
    def random(self, ctrl):
        # not great at reusing bound variables
        ftyp = get_type_system().random_from_class(types.FunType)
        return random_lfun(ftyp, ctrl)

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
        raise types.TypeMismatch(g, f, "Function composition type constraints not met")
    combinator = geach_combinator(g.type, f.type)
    result = (combinator(g)(f)).reduce_all()
    return result



BindingOp.add_op(LFun)



###############
#
# Reduction code
#
###############


def unsafe_variables(fun, arg):
    """For a function and an argument, return the set of variables that are not
    safe to use in application."""
    return arg.free_variables() | fun.free_variables()

def beta_reduce_ts(t, varname, subst):
    if varname in t.free_variables():
        if (t.term() and t.op == varname):
            return subst # TODO copy??
        # we will be changing something in this expression, but not at this
        # level of recursion.
        parts = list()
        for p in t:
            parts.append(beta_reduce_ts(p, varname, subst))
        t = t.copy_local(*parts)
    return t

def variable_replace(expr, m):
    def transform(e):
        return TypedExpr.factory(m[e.op])
    return variable_transform(expr, m.keys(), transform)

def variable_replace_strict(expr, m):
    def transform(e):
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            raise TypeMismatch(e, result, "Strict variable replace failed with mismatched types")
        return result
    return variable_transform(expr, m.keys(), transform)

def variable_replace_unify(expr, m):
    def transform(e):
        ts = get_type_system()
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            unify = ts.unify(result.type, e.type)
            if unify is None:
                raise TypeMismatch(e, result, "Variable replace failed with mismatched types")
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

    r = variable_transform_rebuild(expr, m.keys(), transform)
    return r

def variable_convert(expr, m):
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

def variable_transform_rebuild(expr, dom, fun):
    """Transform free instances of variables in expr, as determined by the
    function fun.

    Operates on a copy.
    expr: a TypedExpr
    dom: a set of variable names
    fun: a function from terms to TypedExprs."""

    targets = dom & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be transformed.
            return fun(expr)
        seq = list()
        dirty = False
        for i in range(len(expr.args)):
            seq.append(variable_transform_rebuild(expr.args[i], targets, fun))
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

def alpha_convert(t, blocklist):
    """ produce an alphabetic variant of t that is guaranteed not to have any
    variables in blocklist.  

    Possibly will not change t."""
    overlap = t.bound_variables() & blocklist
    full_bl = blocklist | t.free_variables() | t.bound_variables()
    # note that this relies on the side effect of alpha_variant...
    conversions = {x : alpha_variant(x, full_bl) for x in overlap}
    return alpha_convert_r(t, overlap, conversions)

def alpha_convert_r(t, overlap, conversions):
    overlap = overlap & t.bound_variables()
    if overlap:
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


###############
#
# Setup
#
###############



global true_term, false_term

# for whatever reason, monkey patching __bool__ doesn't work.
# TODO: is this a good idea?
class FalseTypedTerm(TypedTerm):
    def __bool__(self):
        return False

true_term = TypedTerm("True", types.type_t)
false_term = FalseTypedTerm("False", types.type_t)

def test_setup():
    global ident, ia, ib, P, Q, p, y, t, testf, body, pmw_test1, pmw_test1b, t2
    ident = te("L x_e : x")
    ia = TypedExpr.factory(ident, "y")
    ib = LFun(type_e, ia, "y")
    P = TypedTerm("P", FunType(type_e, type_t))
    Q = TypedTerm("Q", FunType(type_e, type_t))
    x = TypedTerm("x", type_e)
    y = TypedTerm("y", type_e)
    t = TypedExpr.factory(P, x)
    t2 = TypedExpr.factory(Q, x)
    body = TypedExpr.factory("&", t, t) | t
    p = TypedTerm("p", type_t)
    testf = LFun(type_e, body)

    pmw_test1 = LFun(type_t, LFun(type_e, t & p, "x"), "p")
    pmw_test1b = LFun(type_e, t & t2, "x")
    # test: when a free variable in a function scopes under an operator, do not
    # bind the variable on application
    assert pmw_test1.apply(t2) != pmw_test1b

    # Different version of the same test: direct variable substitution
    test2 = TypedExpr.factory("L y_e : L x_e : y_e")
    test2b = TypedExpr.factory("L x_e : x_e")
    assert test2.apply(x) != test2b

def default_variable_type(s):
    #TODO something better
    return type_e

def default_type(s):
    if isinstance(s, TypedExpr):
        return s.type
    elif isinstance(s, Number):
        return type_n
    elif isinstance(s, str):
        t = num_or_str(s)
        if isinstance(t, Number):
            return type_n
        elif is_var_symbol(t):
            return default_variable_type(s)
        else:
            #TODO, better default
            return type_t
    else:
        # TODO: more default special cases?  predicates?
        raise NotImplementedError

def typed_expr(s):
    # class method replaces this.  Call this instead of factory, which has a 
    # slightly different semantics -- factory will make a copy if handed a
    # TypedExpr.
    return TypedExpr.ensure_typed_expr(s)

def is_symbol(s):
    "A string s is a symbol if it starts with an alphabetic char."
    return (isinstance(s, str) and len(s) > 0
                and s[:1].isalpha()
                and not is_multiword(s))

def is_var_symbol(s):
    "A logic variable symbol is an initial-lowercase string."
    return is_symbol(s) and s[0].islower()

def is_multiword(s):
    """a string is multiword if there is intermediate (non-initial and
    non-trailing) whitespace."""
    #TODO this could be more efficient
    return (len(s.strip().split()) != 1)

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
        if isinstance(origin, TypedExpr):
            self.origin = (origin,)
        else:
            self.origin = tuple(origin)
        self.trivial = trivial

    def origin_str(self, latex=False):
        if len(self.origin) == 1:
            if latex:
                return self.origin[0].latex_str()
            else:
                return repr(self.origin[0])
        else:
            if latex:
                return ensuremath("(" +
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
    def __init__(self, steps):
        self.steps = list()
        self.steps_hash = dict()
        if steps is not None:
            self.add_steps(steps)
            self.result = self[-1]
        else:
            self.result = None

    def add_step(self, s):
        self.steps_hash[len(self.steps)] = s
        self.steps.append(s)

    def add_steps(self, steps):
        for s in steps:
            self.add_step(s)

    def __iter__(self):
        return iter(self.steps)

    def __len__(self):
        return len(self.steps)

    def __getitem__(self, i):
        return self.steps[i]

    def steps_sequence(self, latex=False, ignore_trivial=False):
        l = list()
        if len(self.steps) > 0:
            l.append((self.steps[0].origin_str(latex), None, None))
            for i in range(len(self.steps)):
                # assume that origin matches previous result.  Could check this.
                if self.steps[i].trivial and ignore_trivial:
                    continue
                if latex:
                    if self.steps[i].trivial:
                        l.append(("...", self.steps[i].latex_desc,
                                                self.steps[i].subexpression))
                    else:
                        l.append((self.steps[i].result.latex_str(),
                                  self.steps[i].latex_desc,
                                  self.steps[i].subexpression))
                else:
                    l.append((repr(self.steps[i].result),
                                   self.steps[i].desc,
                                   self.steps[i].subexpression))
        return l

    def equality_display(self, content, style=None):
        l = self.steps_sequence(latex=True, ignore_trivial=True)
        n = display.DisplayNode(content=content, parts=[step[0] for step in l],
                                style = display.EqualityDisplay())
        return n

    def build_display_tree(self, recurse=False, parent=None, reason=None,
                                                                style=None):
        defaultstyle = {"align": "left"}
        style = display.merge_styles(style, defaultstyle)
        node_style = display.LRDerivationDisplay(**style)
        l = self.steps_sequence(latex=True)
        parts = list()
        for (expr, subreason, subexpression) in l:
            if reason == "":
                reason = None
            if subexpression and subexpression.derivation and (recurse):
                parts.append(subexpression.derivation.build_display_tree(
                        recurse=recurse,
                        parent=expr,
                        reason=subreason,
                        style=style))
            else:
                parts.append(display.DisplayNode(content=expr,
                        explanation=subreason, parts=None, style=node_style))
        if len(parts) == 0:
            parts = None
        return display.DisplayNode(content=parent, explanation=reason,
                                                parts=parts, style=node_style)

    def trace(self, recurse=True, style=None):
        return self.build_display_tree(recurse=recurse, style=style)

    def show(self, recurse=False, style=None):
        return self.trace(recurse=recurse, style=style)

    def _repr_html_(self):
        return self.build_display_tree(recurse=False)._repr_html_()

    def steps_str(self):
        l = self.steps_sequence(latex=False)
        s = ""
        i = 1
        for (expr, reason, subexpression) in l:
            if reason is None:
                s += "%2i. %s\n" % (i, expr)
            else:
                s += "%2i. %s    (%s)\n" % (i, expr, reason)
            i += 1
        return s

    def __repr__(self):
        return self.steps_str()


def derivation_factory(result, desc=None, latex_desc=None, origin=None,
                                steps=None, subexpression=None, trivial=False):
    """Factory function for `Derivation`s.  See `derived`."""
    if origin is None:
        if steps is not None and len(steps) > 0:
            origin = steps[-1].result
    drv = Derivation(steps)
    # note: will make a copy of the derivation if steps is one; may be better to have something more efficient in the long run
    drv.add_step(DerivationStep(result, desc=desc, origin=origin,
        latex_desc=latex_desc, subexpression=subexpression, trivial=trivial))
    return drv

def derived(result, origin, desc=None, latex_desc=None, subexpression=None,
                                                        allow_trivial=False):
    """Convenience function to return a derived TypedExpr while adding a
    derivational step. Always return result, adds or updates its derivational
    history as a side effect."""
    if isinstance(result, TypedTerm) and result.derivation is None:
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

test_setup()

######################
#
# testing code
#
# * some code for generating random expressions within certain parameters
# * unit tests
#
######################



def repr_parse(e):
    result = te(repr(e), let=False)
    return result == e

random_types = [type_t]
random_ops = ["&", "|", ">>", "%"]

def random_tf_op_expr(ctrl_fun):
    # TODO: not hardcode this
    op = random.choice(random_ops)
    while (op in binary_num_ops):
        op = random.choice(random_ops)
    if op == "~":
        return UnaryNegExpr(ctrl_fun(typ=type_t))
    elif op in binary_symbols_to_op_exprs.keys():
        op_class = binary_symbols_to_op_exprs[op]
        if op_class == eq_factory:
            raise NotImplementedError
        elif op_class == SetContains:
            raise NotImplementedError
        elif issubclass(op_class, BinaryOpExpr):
            if op in binary_num_rels:
                return op_class(ctrl_fun(typ=type_n), ctrl_fun(typ=type_n))
            elif op in binary_tf_ops:
                return op_class(ctrl_fun(typ=type_t), ctrl_fun(typ=type_t))
            else:
                raise NotImplementedError
        else:
            #print(repr(op_class))
            raise NotImplementedError
    else:
        raise NotImplementedError

random_term_base = {type_t : "p", type_e : "x", type_n : "n"}

def random_term(typ=None, blockset=None, usedset=set(), prob_used=0.8,
                                            prob_var=0.5, max_type_depth=1):
    return TypedTerm.random(random_ctrl_fun=None,
                            typ=typ,
                            blockset=blockset,
                            usedset=usedset,
                            prob_used=prob_used,
                            prob_var=prob_var,
                            max_type_depth=max_type_depth)

# use this to try to get more reused bound variables (which tend to have odd
# types when generated randomly)
def random_pred_combo_from_term(output_type, ctrl, usedset):
    ts = get_type_system()
    term = (random.choice(list(usedset))).copy()
    pred_type = ts.unify_ar(term.type, output_type)
    pred = ctrl(typ=pred_type)
    return pred(term)

def random_fa_combo(output_type, ctrl, max_type_depth=1):
    ts = get_type_system()
    input_type = ts.random_type(max_type_depth, 0.5, allow_variables=False)
    fun_type = types.FunType(input_type, output_type)
    result = (ctrl(typ=fun_type))(ctrl(typ=input_type))
    return result

def random_lfun(typ, ctrl):
    global random_used_vars
    typ = get_type_system().unify(typ, tp("<?,?>"))
    input_type = typ.left
    body_type = typ.right
    variable = random_term(input_type, usedset=random_used_vars, prob_used=0.2,
                                                        prob_var=1.0)
    random_used_vars |= {variable}
    return LFun(variable, ctrl(typ=body_type))

def random_lfun_force_bound(typ, ctrl):
    global random_used_vars
    typ = get_type_system().unify(typ, tp("<?,?>"))
    input_type = typ.left
    body_type = typ.right
    variable = random_term(input_type, usedset=random_used_vars, prob_used=0.2,
                                                        prob_var=1.0)
    random_used_vars |= {variable}
    return LFun(variable, random_pred_combo_from_term(body_type, ctrl,
                                                    usedset=random_used_vars))


def random_binding_expr(ctrl, max_type_depth=1):
    global random_used_vars
    ts = get_type_system()
    options = [ForallUnary, ExistsUnary, ExistsExact]
    op_class = random.choice(options)
    var_type = ts.random_type(max_type_depth, 0.5)
    variable = random_term(var_type, usedset=random_used_vars, prob_used=0.2,
                                                                prob_var=1.0)
    random_used_vars |= {variable}
    return op_class(variable, ctrl(typ=type_t))

def random_from_class(cls, max_depth=1, used_vars=None):
    global random_used_vars
    if used_vars is None:
        used_vars = set()
    random_used_vars = used_vars

    def ctrl(**args):
        global random_used_vars
        return random_expr(depth=max_depth-1, used_vars=random_used_vars,
                                                                    **args)

    return cls.random(ctrl)


# ugh, need to find a way to do this not by side effect
global random_used_vars
random_used_vars = set()

def random_expr(typ=None, depth=1, used_vars=None):
    """Generate a random expression of the specified type `typ`, with an AST of
    specified `depth`. Leave used_vars as None for expected behavior.

    This won't generate absolutely everything, and I haven't tried to make this
    use some sensible distribution over expressions (whatever that would be).
    If typ is None, it will draw from the random_types module level variable,
    which is currently just [type_t].

    An alternative approach would be to generate a random AST first, and fill
    it in.
    """
    global random_used_vars
    if used_vars is None:
        used_vars = set()
    random_used_vars = used_vars
    if typ is None:
        typ = random.choice(random_types)
    if depth == 0:
        term = random_term(typ, usedset=random_used_vars)
        random_used_vars |= {term}
        return term
    else:
        # possibilities:
        #  1. any typ: function-argument combination resulting in typ
        #  2. if typ is type_t: operator expression of typ (exclude non type_t
        #     options for now)
        #  3. if typ is type_t: binding expression of type_t
        #  4. if typ is functional: LFun of typ
        # ignore sets for now (variables with set types can be generated as
        # part of option 1)
        # ignore iota for now
        options = [1]
        if typ == type_t:
            options.append(2)
            options.append(3)
        if typ.functional():
            options.append(4)
            options.append(5)
        if depth == 1 and len(random_used_vars) > 0:
            options.extend([6,7,8,9]) # try to reuse vars a bit more
        choice = random.choice(options)
        def ctrl(**args):
            global random_used_vars
            return random_expr(depth=depth-1, used_vars=random_used_vars,
                                                                        **args)
        if choice == 1:
            return random_fa_combo(typ, ctrl)
        elif choice == 2:
            return random_tf_op_expr(ctrl)
        elif choice == 3:
            return random_binding_expr(ctrl)
        elif choice == 4:
            return random_lfun(typ, ctrl)
        elif choice == 5:            
            return random_lfun_force_bound(typ, ctrl)
        elif choice >= 6:
            return random_pred_combo_from_term(typ, ctrl, random_used_vars)
        else:
            raise NotImplementedError

import unittest

def test_repr_parse_abstract(self, depth):
    for i in range(1000):
        x = random_expr(depth=depth)
        result = repr_parse(x)
        latex_str = x.latex_str() # also test that this doesn't crash -- can't
                                  # easily test actual contents.
        if not result:
            print("Failure on depth %i expression '%s'" % (depth, repr(x)))
        self.assertTrue(result)

def testsimp(self, a, b):
    intermediate = a.simplify()
    teb = te(b)
    if intermediate != teb:
        print("Failed simplification test: '%s == %s'" % (repr(a), repr(b)))
    self.assertEqual(intermediate, teb)
    return intermediate

te_classes = [ApplicationExpr, Tuple, TypedTerm, Partial, Disjunctive, 
              UnaryNegExpr, UnaryNegativeExpr, BinaryAndExpr, BinaryOrExpr,
              BinaryArrowExpr, BinaryBiarrowExpr, BinaryNeqExpr, BinaryLExpr,
              BinaryLeqExpr, BinaryGExpr, BinaryGeqExpr, BinaryPlusExpr,
              BinaryMinusExpr, BinaryDivExpr, BinaryExpExpr, SetContains,
              TupleIndex, ConditionSet, ListedSet, ForallUnary, ExistsUnary,
              ExistsExact, IotaUnary, IotaPartial, LFun]

class MetaTest(unittest.TestCase):
    def setUp(self):
        self.ident = te("L x_e : x") 
        self.ia = TypedExpr.factory(self.ident, "y")
        self.ib = LFun(type_e, self.ia, "y")
        self.P = TypedTerm("P", FunType(type_e, type_t))
        self.Q = TypedTerm("Q", FunType(type_e, type_t))
        self.x = TypedTerm("x", type_e)
        self.y = TypedTerm("y", type_e)
        self.t = TypedExpr.factory(self.P, self.x)
        self.t2 = TypedExpr.factory(self.Q, self.x)
        self.body = TypedExpr.factory("&", self.t, self.t) | self.t
        self.p = TypedTerm("p", type_t)
        self.testf = LFun(type_e, self.body)

    def test_basic(self):
        # equality basics
        self.assertEqual(self.P, self.P)
        self.assertEqual(self.x, self.x)
        self.assertEqual(self.testf, self.testf)
        self.assertNotEqual(self.P, self.Q)
        self.assertNotEqual(self.x, self.y)


    def test_class_random(self):
        for c in te_classes:
            for i in range(50):
                random_from_class(c)

    def test_copy(self):
        for c in te_classes:
            for i in range(50):
                x = random_from_class(c)
                self.assertEqual(x, x.copy())
                self.assertEqual(x, x.copy_local(*x))


    def test_parse(self):
        # overall: compare parsed TypedExprs with constructed TypedExprs
        # basic operator syntax
        self.assertEqual(TypedExpr.factory(
            "(P_<e,t>(x_e) & P_<e,t>(x_e)) | P_<e,t>(x_e)"), self.body)
        # parenthesis reduction
        self.assertEqual(TypedExpr.factory(
            "((P_<e,t>(x_e) & P_<e,t>(x_e)) | (P_<e,t>(x_e)))"), self.body)
        # parenthesis grouping
        self.assertNotEqual(TypedExpr.factory(
            "P_<e,t>(x_e) & (P_<e,t>(x_e) | P_<e,t>(x_e))"), self.body)
        # variable binding syntax
        self.assertEqual(TypedExpr.factory("L x_e : x_e"), self.ident)
        self.assertRaises(parsing.ParseError, TypedExpr.factory, "L x_e : x_t")
        logger.setLevel(logging.WARNING)
        te("L x: L y: In(y)(x)")
        logger.setLevel(logging.INFO)

    def test_reduce(self):
        self.assertEqual(self.ident(self.y).reduce(), self.y)

        # test: when a free variable in a function scopes under an operator, do
        # not bind the variable on application        
        pmw_test1 = LFun(type_t, LFun(type_e, self.t & self.p, "x"), "p")
        pmw_test1b = LFun(type_e, self.t & self.t2, "x")
        self.assertNotEqual(pmw_test1.apply(self.t2), pmw_test1b)

        # Different version of the same test: direct variable substitution
        test2 = TypedExpr.factory("L y_e : L x_e : y_e")
        test2b = TypedExpr.factory("L x_e : x_e")
        self.assertNotEqual(test2.apply(self.x), test2b)

        # test for accidental collisions from alpha conversions, added Apr 2015
        test3 = TypedExpr.factory(
            "(L xbar_<e,t> : L x_e : xbar(x))(L z_e : P_<(e,e,e),t>(x_e,z_e, x1_e))")
        test3 = test3.reduce_all()
        self.assertNotEqual(test3[1][1][0], test3[1][1][1])
        self.assertNotEqual(test3[1][1][0], test3[1][1][2])
        self.assertNotEqual(test3[1][1][1], test3[1][1][2])

    def test_polymorphism(self):
        # geach combinator test
        g = te("L g_<Y,Z> : L f_<X,Y> : L x_X : g(f(x))")
        self.assertEqual(g.try_adjust_type(tp("<<e,t>,<<e,e>,?>>")),
            te("(λ g_<e,t>: (λ f_<e,e>: (λ x_e: g_<e,t>(f_<e,e>(x_e)))))"))
        self.assertEqual(g.let_type(tp("<?,<<<e,t>,?>,?>>")),
            te("(λ g_<Y,Z>: (λ f_<<e,t>,Y>: (λ x_<e,t>: g_<Y,Z>(f_<<e,t>,Y>(x_<e,t>)))))"))
        # z combinator test
        z = te("(λ f_<X,<e,Z>>: (λ g_<e,X>: (λ x_e: f(g(x))(x))))")
        self.assertEqual(z.try_adjust_type(tp("<<e,<e,t>>,?>")),
            te("(λ f_<e,<e,t>>: (λ g_<e,e>: (λ x_e: f_<e,<e,t>>(g_<e,e>(x_e))(x_e))))"))


    def test_binary_simplify(self):
        # negation
        testsimp(self, te("~False"), True)
        testsimp(self, te("~True"), False)
        testsimp(self, te("~p_t"), te("~p_t"))

        # conjunction
        testsimp(self, te("True & True"), True)
        testsimp(self, te("True & False"), False)
        testsimp(self, te("False & True"), False)
        testsimp(self, te("False & False"), False)
        testsimp(self, te("False & p_t"), False)
        testsimp(self, te("p_t & False"), False)
        testsimp(self, te("True & p_t"), te("p_t"))
        testsimp(self, te("p_t & True"), te("p_t"))
        testsimp(self, te("p_t & p_t"), te("p_t"))
        testsimp(self, te("p_t & q_t"), te("p_t & q_t"))

        # disjunction
        testsimp(self, te("True | True"), True)
        testsimp(self, te("True | False"), True)
        testsimp(self, te("False | True"), True)
        testsimp(self, te("False | False"), False)
        testsimp(self, te("False | p_t"), te("p_t"))
        testsimp(self, te("p_t | False"), te("p_t"))
        testsimp(self, te("True | p_t"), True)
        testsimp(self, te("p_t | True"), True)
        testsimp(self, te("p_t | p_t"), True)
        testsimp(self, te("p_t | q_t"), te("p_t | q_t"))

        # arrow
        testsimp(self, te("True >> True"), True)
        testsimp(self, te("True >> False"), False)
        testsimp(self, te("False >> True"), True)
        testsimp(self, te("False >> False"), True)
        testsimp(self, te("False >> p_t"), True)
        testsimp(self, te("p_t >> False"), te("~p_t"))
        testsimp(self, te("True >> p_t"), te("p_t"))
        testsimp(self, te("p_t >> True"), True)
        testsimp(self, te("p_t >> p_t"), True)
        testsimp(self, te("p_t >> q_t"), te("p_t >> q_t"))

        # biconditional
        testsimp(self, te("True <=> True"), True)
        testsimp(self, te("True <=> False"), False)
        testsimp(self, te("False <=> True"), False)
        testsimp(self, te("False <=> False"), True)
        testsimp(self, te("False <=> p_t"), te("~p_t"))
        testsimp(self, te("p_t <=> False"), te("~p_t"))
        testsimp(self, te("True <=> p_t"), te("p_t"))
        testsimp(self, te("p_t <=> True"), te("p_t"))
        testsimp(self, te("p_t <=> q_t"), te("p_t <=> q_t"))
        testsimp(self, te("p_t <=> p_t"), True)

        # neq
        testsimp(self, te("True =/= True"), False)
        testsimp(self, te("True =/= False"), True)
        testsimp(self, te("False =/= True"), True)
        testsimp(self, te("False =/= False"), False)
        testsimp(self, te("False =/= p_t"), te("p_t"))
        testsimp(self, te("p_t =/= False"), te("p_t"))
        testsimp(self, te("True =/= p_t"), te("~p_t"))
        testsimp(self, te("p_t =/= True"), te("~p_t"))
        testsimp(self, te("p_t =/= q_t"), te("p_t =/= q_t"))
        testsimp(self, te("p_t =/= p_t"), False)

    # each of these generates 1000 random expressions with the specified depth,
    # and checks whether their repr parses as equal to the original expression
    def test_repr_parse_0(self): test_repr_parse_abstract(self, 0)
    def test_repr_parse_1(self): test_repr_parse_abstract(self, 1)
    def test_repr_parse_2(self): test_repr_parse_abstract(self, 2)
    # def test_repr_parse_3(self): test_repr_parse_abstract(self, 3)
    # def test_repr_parse_4(self): test_repr_parse_abstract(self, 4)
    # def test_repr_parse_5(self): test_repr_parse_abstract(self, 5)
    # def test_repr_parse_6(self): test_repr_parse_abstract(self, 6)



