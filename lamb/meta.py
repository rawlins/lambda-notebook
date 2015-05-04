#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re, logging, random
from numbers import Number
from lamb import types, utils, parsing, display
from lamb.types import TypeMismatch, type_e, type_t, type_n, type_property, type_transitive, BasicType, FunType
from lamb.utils import *
#import logic, utils

global logger
def setup_logger():
    """Set up a module-level logger called `logger` for use across `lamb` modules."""
    global logger
    logger = logging.getLogger("lambda")
    logger.handlers = list() # otherwise, will get double output on reload (since this just keeps adding handlers)
    logger.setLevel(logging.INFO)
    logger.propagate = False
    # note that basicConfig does _not_ work for interactive ipython sessions, including notebook.
    ch = logging.StreamHandler()
    #ch.setLevel(logging.INFO)
    ch.setFormatter(logging.Formatter('%(levelname)s (%(module)s): %(message)s'))
    logger.addHandler(ch)

setup_logger()

global _constants_use_custom, _type_system
_constants_use_custom = False

global _parser_assignment
_parser_assignment = None

def constants_use_custom(v):
    """Set whether constants use custom display routines."""
    global _constants_use_custom
    _constants_use_custom = v

# TODO: could consider associating TypedExpr with a type system rather than using the global variable.
# advantages: generality.  Disadvantages: may be a little pointless in practice?
def set_type_system(ts):
    """Sets the current type system for the metalanguage.  This is a global setting."""
    global _type_system
    _type_system = ts

def get_type_system():
    """Gets the current (global) type system for the metalanguage."""
    return _type_system

def ts_unify(a, b):
    """Calls the current type system's `unify` function on types `a` and `b`.  This returns a unified type, or `None` if the two can't be unified."""
    ts = get_type_system()
    return ts.unify(a, b)

def ts_compatible(a, b):
    """Returns `True` or `False` depending on whether `a` and `b` are compatible types."""
    ts = get_type_system()
    return ts.unify(a,b) is not None

def tp(s):
    """Convenience wrapper for the current type system's type parser."""
    ts = get_type_system()
    result = ts.type_parser(s)
    return result

def te(s, assignment=None):
    """Convenience wrapper for `lang.TypedExpr.factory`."""
    return TypedExpr.factory(s, assignment=assignment)

def term(s, typ=None, assignment=None):
    """Convenience wrapper for building terms.
    `s`: the term's name.
    `typ`: the term's type, if specified."""
    return TypedTerm.term_factory(s, typ=typ, assignment=assignment)

#_type_system = types.UnderTypeSystem()
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


def merge_type_envs(env1, env2, target=None):
    """Merge two type environments.  A type environment is simply an assignment, where the mappings to terms are used to define types.
    Other mappings are ignored.

    If `target` is set, it specifies a set of variable names to specifically target; anything not in it is ignored.
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
                raise TypeMismatch(env1[k1], env2[k1], "Failed to unify types across distinct instances of term")
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



class TypedExpr(object):
    """Basic class for a typed n-ary logical expression in a formal language.  This class should generally be
    constructed using the factory method, not the constructor.

    Three key fields:
      * type: an object that implements the type interface.
      * op: an object representing the operator in the expression.
      * args: _n_ args representing the arguments (if any) to the operator.

    The op field:
      * may be a string representing the operator symbol.  This case mostly covers special hard-coded logical/numeric operators.  
        May be used in subclasses such as LFun.  NOTE: for hard-coded operators this is now deprecated, call the factory function.
      * May be itself a TypedExpr.  (For example, an LFun with the right type.)
        If so, there must be exactly one argument of the correct type.
      * May be a term name, treating this case as either a 0-ary operator or an unsaturated term.  
        Note that right now, this _only_ occurs in subclasses.  (TypedTerm)

    originally based on logic.Expr (from aima python), now long diverged.
    """
    def __init__(self, op, *args, defer=False):
        """
        Constructor for TypedExpr class.  This should generally not be called directly, rather, the factory function should be used.  In
        fact, TypedExpr is not currently ever directly instantiated.

        This is intended only for calls from subclass `__init__`.  It (at this stage) amounts to a convenience function that sets some
        common variables -- a subclass that does not call this should ensure that these are all set.  self.args must be a list (not a tuple).

        WARNING: this function does not set self.type, which _must_ be set.  It does not perform any type-checking.

        `defer`: annotate with this if the TypedExpr does not conform to type constraints.  (Useful for derivational histories or error reports.)
        """
        self.type_guessed = False
        self.derivation = None
        self.defer = defer

        if (len(args) == 0):
            logger.warning("Vacuous container TypedExpr")
            args = list()

        self.op = op
        self.args = list(args)

    def try_adjust_type(self, new_type, derivation_reason=None, assignment=None):
        """Attempts to adjust the type of `self` to be compatible with `new_type`.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        #unify_a, unify_base = ts.local_unify(new_type, self.type)
        #unify_target = ts.unify(self.type, new_type)

        # if the two are alpha equivalents, the following call with this order should return new_type
        unify_target = ts.unify(new_type, self.type)
        #print("new_type %s self type %s unify_a %s unify_target %s" % (new_type, self.type, unify_a, unify_target))
        if unify_target is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_target:
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            if isinstance(self.op, TypedExpr):
                if len(self.args) != 1:
                    # TODO improve
                    raise ValueError("Wrong number of arguments on type adjustment")
                    #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
                    #return None
                #new_op_type = types.FunType(self.args[0].type, unify_target)
                (new_op_type, new_arg_type, new_ret_type) = ts.unify_fr(self.op.type, unify_target, type_env=assignment)
                if new_op_type is None:
                    return None
                new_op = self.op.try_adjust_type(new_op_type, derivation_reason=derivation_reason, assignment=assignment)
                if new_op is None:
                    return None
                new_arg = self.args[0].try_adjust_type(new_arg_type, derivation_reason=derivation_reason, assignment=assignment)
                if new_arg is None:
                    return None
                self_copy = self.copy()
                self_copy.op = new_op
                self_copy.args = [new_arg]
                #self_copy.type = new_op.type.right
                return derived(self_copy, self, derivation_reason)
            else:
                # should be term?
                if self.term():
                    new_term = self.copy()
                    new_term.type = unify_target
                    if assignment is not None and new_term.op in assignment:
                        assignment[new_term.op] = new_term
                    return derived(new_term, self, derivation_reason)
                else:
                    logger.warning("In type adjustment, unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_target))
                    return self

    def subst(self, i, s, assignment=None):
        """ Tries to consistently (relative to types) substitute s for element i of the TypedExpr.

        Will return a modified copy.
        """
        s = TypedExpr.ensure_typed_expr(s)
        if i == 0:
            old = self.op
        else:
            old = self.args[i-1]
        if not isinstance(old, TypedExpr):
            raise ValueError("Cannot perform substitution on non-TypedExpr %s" % (old))
        c = self.copy()
        ts = get_type_system()
        # check: is the type of the substitution compatible with the type of what it is replacing?
        unified = ts.unify(old.type, s.type)
        #print("%s, %s" % (unify_a, unify_b))
        if unified is None:
            raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
        if unified != s.type:
            # compatible but unify suggested a new type for the substitution.  
            # Try adjusting the type of the expression.
            s_a = s.try_adjust_type(unified)
            if s_a is None:
                raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
            #print("adjusting %s to %s" % (s,s_a))
            s = s_a
        if i == 0:
            # the position is the operator position, need some special logic.  May have to adjust the types of 
            # the argument and the output
            c.op = s
            # TODO: used to check if op was functional.  This shouldn't arise any more?
            unify_f, unify_arg, unify_out = ts.unify_fa(c.op.type, c.args[0].type, type_env=assignment)
            if unify_f is None:
                raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
            if unify_arg != c.args[0].type:
                new_arg = c.args[0].try_adjust_type(unify_arg)
                if new_arg is None:
                    raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
                c.args[0] = new_arg
            c.type = unify_out
        else:
            c.args[i-1] = s
            if isinstance(c.op, TypedExpr):
                # op must be functional, make sure it is compatible with its new input
                unify_f, unify_arg, unify_out = ts.unify_fa(c.op.type, c.args[0].type, type_env=assignment)
                if unify_f is None:
                    raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
                if unify_f != c.op.type:
                    new_op = c.op.try_adjust_type(unify_f)
                    if new_op is None:
                        raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
                    c.op = new_op
                c.type = unify_out
            else:
                pass
                # use a strict substitution rule for the time being
                #if unify_a != old.type:
                #    raise TypeMismatch(old, s, "Unify suggested strengthened type %s, but cannot accommodate" % unify_a)
                # or, silently succeed here?
                #raise NotImplementedError("Non-TypedExpr '%s' in subst" % c.op)
        return c

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
        return cls.try_parse_paren_struc_r(struc, assignment=assignment, locals=locals)


    @classmethod
    def try_parse_flattened(cls, s, assignment=None, locals=None):
        """Attempt to parse a flat, simplified string into a TypedExpr.  Binding expressions should be already handled.
        assignment: a variable assignment to use when parsing.
        locals: a dict to use as the local variables when parsing.

        Do some regular expression magic to expand metalanguage terms into constructor/factory calls, 
        and then call eval.

        The gist of the magic (see expand_terms):
          * replace some special cases with less reasonable operator names.  (This is based on AIMA logic.py)
          * find things that look like term names, and surround them with calls to the term factory function.

        Certain special case results are wrapped in TypedExprs, e.g. sets and tuples.
        """
        if locals is None:
            locals = dict()
        ## Replace the alternative spellings of operators with canonical spellings
        s = s.replace('==>', '>>').replace('<==', '<<')
        s = s.replace('<=>', '%').replace('=/=', '^')
        s = TypedExpr.expand_terms(s, assignment=assignment, ignore=locals.keys())
        ## Now eval the string.  (A security hole; do not use with an adversary.)
        # TODO: this won't necessarily do the right thing with assignment, can still result in inconsistent types
        #print(s)
        lcopy = locals.copy()
        lcopy.update({'TypedExpr':TypedExpr,'TypedTerm':TypedTerm, 'assignment': assignment, 'type_e': type_e})
        #print("eval: " + s)

        # cannot figure out a better way of doing this short of actually parsing
        global _parser_assignment
        _parser_assignment = assignment # not remotely thread-safe, if that becomes an issue
        result = eval(s, dict(), lcopy) 
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
    def try_parse_binding_struc(cls, s, assignment=None, locals=None, vprefix="ilnb"):
        """Try to parse `s` as a binding operator expression.  Will return a subclass of BindingOp, None, or raise a `parsing.ParseError`.

        the variable on the exception `met_preconditions` is used to attempt to figure out whether this was a plausible attempt at a 
        binding operator expression, so as to get the error message right."""
        try:
            return BindingOp.try_parse_binding_struc_r(s, assignment=assignment, locals=locals, vprefix=vprefix)
        except parsing.ParseError as e:
            if not e.met_preconditions:
                return None
            else:
                raise e

    @classmethod
    def try_parse_paren_struc_r(cls, struc, assignment=None, locals=None, vprefix="ilnb"):
        """Recursively try to parse a semi-AST with parenthetical structures matched."""
        #print("test: " + repr(struc))
        expr = cls.try_parse_binding_struc(struc, assignment=assignment, locals=locals, vprefix=vprefix)
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
                sub_expr = cls.try_parse_paren_struc_r(sub, assignment=assignment, locals=locals, vprefix=vprefix)
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
        # TODO: generalize to arbitrary types!
        # deal with basic types first
        ts = get_type_system()
        result = ts.type_parser(s)
        return result

    @classmethod
    def try_parse_typed_term(cls, s, assignment=None, strict=False):
        """Try to parse string 's' as a typed term.
        assignment: a variable assignment to parse s with.

        Format: n_t
          * 'n': a term name.  
            - initial numeric: term is a number.
            - initial alphabetic: term is a variable or constant.  (Variable: lowercase initial.)
          * 't': a type, optional.  If absent, will either get it from assignment, or return None as the 2nd element.

        Returns a tuple of a variable name, and a type.  If you want a TypedTerm, call one of the factory functions.
        Raises: TypeMismatch if the assignment supplies a type inconsistent with the specified one.
        """
        v, typ, end = cls.parse_term(s, i=0, return_obj=False, assignment=assignment)
        if strict and end < len(s):
            remainder = s[end:].strip()
            if len(remainder) > 0:
                raise parsing.ParseError("Extra characters ('%s') in binding operator term following variable" % remainder, s, i=end, met_preconditions=True)
        return (v, typ)

    @classmethod
    def find_term_locations(cls, s, i=0):
        """Find locations in a string `s` that are term names."""
        term_re = re.compile(r'([a-zA-Z0-9]+)(_)?')
        unfiltered_result = parsing.find_pattern_locations(term_re, s, i=i, end=None)
        result = list()
        for r in unfiltered_result:
            if r.start() > 0 and s[r.start() - 1] == ".":
                # result is prefaced by a ".", and therefore is a functional call or attribute
                continue
            result.append(r)
        return result

    @classmethod
    def expand_terms(cls, s, i=0, assignment=None, ignore=None):
        """Treat terms as macros for term_factory calls.  Attempt to find all term strings, and replace them with eval-able factory calls.

        This is an expanded version of the original regex approach; one reason to move away from that is that this will truely parse the types."""
        terms = cls.find_term_locations(s, i)
        if ignore is None:
            ignore = set()
        offset = 0
        for t in terms:
            if t.start() + offset < i:
                # parsing has already consumed this candidate term, ignore.  (E.g. an "e" in a type signature.)
                continue
            #print("parsing '%s' at: '%s'" % (t.group(0), s[t.start()+offset:]))
            (name, typ, end) = cls.parse_term(s, t.start() + offset, return_obj=False, assignment=assignment)
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
        """Parse position `i` in `s` as a term expression.  A term expression is some alphanumeric sequence
        followed optionally by an underscore and a type.  If a type is not specified locally, but is present in 
        `assignment`, use that.  If a type is specified and is present in `assignment`, check type compatibility 
        immediately."""
        ts = get_type_system()
        term_name, next = parsing.consume_pattern(s, i, r'([a-zA-Z0-9]+)(_)?', return_match=True)
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
        if (assignment is not None):
            if typ is None:
                if term_name.group(1) in assignment:
                    # inherit type from context
                    typ = assignment[term_name.group(1)].type
            else:
                if term_name.group(1) in assignment:
                    unified = ts.unify(typ, assignment[term_name.group(1)].type)
                    if unified is None:
                        raise TypeMismatch(cls.term_factory(term_name.group(1), typ), assignment[term_name.group(1)], "Failed to unify with type specified by assignment")
                    else:
                        # TODO: better logic?
                        typ = unified

        if return_obj:
            # should call a factory function here, need to resolve circularity first.
            #term = TypedTerm(term_name.group(1), typ=typ, assignment=assignment)
            term = cls.term_factory(term_name.group(1), typ=typ, assignment=assignment, preparsed=True)
            return (term, end)
        else:
            return (term_name.group(1), typ, end)

    @classmethod
    def term_factory(cls, s, typ=None, assignment=None, preparsed=False):
        """Attempt to construct a TypedTerm from argument s.

        If s is already a TypedTerm, return a copy of the term.
        If s is a string, try to parse the string as a term name.  (see try_parse_typed_term)
        Otherwise, fail.
        """
        # TODO: if handed a complex TypedExpr, make a term referring to it??
        #print("term factory '%s', assignment=%s" % (s, assignment))
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
            if typ is not None:
                type_vars = typ.bound_type_vars()
                #if len(type_vars) > 0 and not v in assignment:
                #    raise TypeMismatch(TypedTerm(v, typ=typ), None, "Cannot use type variables in non-declared or free terms.")
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
          * single arg, is a TypedExpr: will return a copy of that arg.  (See ensure_typed_expr for alternate semantics.)
          * single arg, is a number: will return a TypedTerm using that number.
          * single arg, is a variable/constant name: will return a TypedTerm using that name.  (Happens in parser magic.)
          * single arg, complex expression: will parse it using python syntax. (Happens in parser magic.)
          * multiple args: call the standard constructor.
        """
        ### NOTE: do not edit this function lightly...
        #print("    factory: args %s" % repr(args))
        #if assignment is None:
        #    assignment = {}
        global _parser_assignment
        if assignment is None:
            if _parser_assignment is None:
                assignment = dict()
            else:
                assignment = _parser_assignment # not remotely thread-safe, if that becomes an issue
        if len(args) == 1 and isinstance(args[0], TypedExpr):
            # handing this a single TypedExpr always returns a copy of the object.  I set this case aside for clarity.
            # subclasses must implement copy() for this to work right.
            return args[0].copy()
        if len(args) == 0:
            return None #TODO something else?
        elif len(args) == 1:
            # args[0] is either an unsaturated function, a term, or a string that needs parsed.
            # in the first two cases, return a unary TypedExpr
            s = args[0]
            if isinstance(s, Number): 
                return TypedTerm(s, type_n)
            elif s is True:
                return true_term
            elif s is False:
                return false_term
            elif isinstance(s, str):
                #return cls.parse_expr_string(s, assignment)
                return cls.parse(s, assignment)
            else:
                raise NotImplementedError
        else:
            # Argument length > 1.  
            # This code path is for constructing complex TypedExprs where args[0] must be a function / operator.
            # Will potentially recurse via ensure_typed_expr on all arguments.

            if isinstance(args[0], str):
                if args[0] in op_symbols:
                    return op_expr_factory(*args) # args[0] is a special-cased operator symbol
            arg0 = cls.ensure_typed_expr(args[0])

            # this is redundant with the constructor, but I can't currently find a way to simplify.
            # after this point, all elements of args will be TypedExprs.
            args = (arg0,) + tuple([cls.ensure_typed_expr(a) for a in args[1:]])

            # package longer arg lengths in Tuples.  After this point, len(args) can only be 2.
            if len(args) > 2:
                packaged_args = Tuple(args[1:])
                args = (args[0], packaged_args)
            if (not args[0].type.functional()) and args[0].type_guessed:
                # special case: see if the type of the operator is guessed and coerce accordingly
                # TODO: should type t be the default return type?

                # prevent future coercion of the argument
                args[1].type_not_guessed()
                coerced_op = args[0].try_coerce_new_argument(args[1].type, assignment=assignment)
                if coerced_op is not None:
                    logger.info("Coerced guessed type %s for '%s' into %s, to match argument '%s'" % (args[0].type, repr(args[0]), coerced_op.type, repr(args[1])))
                    args = (coerced_op,) + args[1:]
                else:
                    logger.warning("Unable to coerce guessed type %s for '%s' to match argument '%s' (type %s)" % (args[0].type, repr(args[0]), repr(args[1]), args[1].type))
            # if we get to this point, args[0] should be the operator, and the rest of the list arguments to the operator.
            #return TypedExpr(*args)
            return ApplicationExpr(*args, assignment=assignment)

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
                raise ValueError("Do not know how to ensure TypedExpr for '%s'" % repr(s))
        if typ is None:
            return result
        else:
            r_adjusted = result.try_adjust_type(typ, assignment=assignment)
            if r_adjusted is None:
                raise TypeMismatch(result, typ, mode="type adjustment")
            else:
                return r_adjusted

    def try_coerce_new_argument(self, typ, remove_guessed=False, assignment=None):
        """For guessed types, see if it is possible to coerce a new argument.  Will recurse to
        find guessed types.

        This is not type inference.  Rather, it is a convenience shorthand for writing n-ary extensional predicates without type annotation."""
        if not self.type_guessed:
            return None
        if not isinstance(self.op, TypedExpr):
            return None
        result = self.op.try_coerce_new_argument(typ, assignment=assignment)
        if result:
            #copy = TypedExpr(result, *self.args)
            copy = ApplicationExpr(result, *self.args)
            if (remove_guessed):
                result.type_guessed = False
            return copy
        else:
            return None

    def type_not_guessed(self):
        """Recursively set that the type of `self` is not a guess."""
        self.type_guessed = False
        if isinstance(self.op, TypedExpr):
            self.op.type_not_guessed()

    def copy(self):
        """Make a copy of the expression.  Will not produce a deep copy.

        Must be overridden by subclasses, or this will go wrong.
        """
        # TODO should this call the factory?
        raise NotImplementedError
        c = TypedExpr(self.op, *self.args, defer=self.defer)
        #c.derivation = self.derivation #TODO: should I do this?
        #print(c.type, self.type, c, self, self.op, self.args[0])
        #assert c == self
        # if c != self:
        #     raise Exception(c, self)
        return c

    def local_copy(self, *args):
        raise NotImplementedError

    def type_env(self, constants=False, target=None):
        env = dict()
        for part in self:
            if isinstance(part, TypedExpr):
                env = merge_type_envs(env, part.type_env(constants=constants, target=target))
        return env

    def regularize_type_env(self, assignment=None, constants=False, target=None):
        if assignment is None:
            assignment = dict()
        env = merge_type_envs(self.type_env(constants=constants, target=target), assignment, target=target)
        # if env and len(env) > 0:
        #     print("        regularize: ", repr(env))
        return self.under_assignment(env)


    def compact_type_vars(self, target=None, unsafe=None):
        env = self.type_env(constants=True, target=target)
        tvars = types.vars_in_env(env)
        if len(tvars) == 0:
            return self
        compacted_map = types.compact_type_set(tvars, unsafe=unsafe)
        return self.under_type_assignment(compacted_map)

    def under_type_assignment(self, mapping):
        #dirty = False
        parts = list()
        copy = self.copy()
        for part in copy:
            if isinstance(part, TypedExpr):
                new_part = part.under_type_assignment(mapping)
            else:
                new_part = part
            parts.append(new_part)
        copy.type = copy.type.sub_type_vars(mapping)
        return copy.local_copy(*parts)


    def alpha_rename_type_vars(self, blocklist, type_assignment=None):
        if type_assignment is None:
            type_assignment=dict()
        dirty = False
        n = list()
        for part in self:
            if isinstance(part, TypedExpr):
                new_part = part.alpha_rename_type_vars(blocklist, type_assignment)
                if new_part is not part:
                    dirty = True
            else:
                new_part = part
            n.append(new_part)
        if dirty:
            return self.local_copy(*parts)
        else:
            return self

    def under_assignment(self, assignment):
        """Use `assignment` to replace any appropriate variables in `self`."""
        # do this first so that any errors show up before the recursive step
        if assignment is None:
            a2 = dict()
        else:
            a2 = {key: self.ensure_typed_expr(assignment[key]) for key in assignment}
        #return variable_replace_strict(self, a2)
        return variable_replace_unify(self, a2)

    # the next sequence of functions is clearly inefficient, and could be replaced by memoization (e.g. 'director strings' or 
    # whatever).  But I don't think it matters for this application.
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
        """Find the set of variables that are bound (somewhere) in a typed expression.

        Note that this may be overlapping with the set of free variables.
        """
        result = set()
        if isinstance(self.op, TypedExpr):
            result.update(self.op.bound_variables())

        for a in self.args:
            if isinstance(a, TypedExpr):
                result.update(a.bound_variables())
        return result

    def find_safe_variable(self, starting="x"):
        """Find an a safe alpha variant of the starting point (by default: 'x'), that is not used in the expression."""
        blockset = self.free_variables() | self.bound_variables()
        varname = alpha_variant(starting, blockset)
        return varname

    def term(self):
        return (isinstance(self.op, str) and len(self.args) == 0)

    def atomic(self):
        if isinstance(self.op, TypedExpr):
            return False
        for a in self.args:
            if isinstance(a, TypedExpr):
                return False
        return True

    def reducible(self):
        if len(self.args) == 1 and isinstance(self.op, LFun):
            return True
        return False

    def reduce(self):
        """if there are arguments to op, see if a single reduction is possible."""
        if not self.reducible():
            return self
        if isinstance(self.op, LFun):
            return derived(self.op.apply(self.args[0]), self, desc="Beta reduction")
        else:
            # functional op but don't know what to do
            # TODO: implement some special casing here?
            #   in particular, constant terms, numeric ops, TF ops
            return self

    def reduce_sub(self, i):
        """Applies reduce to a constituent term, determined by i.

        i is indexed with 0 as the operator, successive numbers any arguments."""
        if i == 0:
            if isinstance(self.op, TypedExpr):
                new_op = self.op.reduce()
                if new_op is not self.op:
                    result = self.copy()
                    result.op = new_op
                    return derived(result, self, desc="Reduction of op")
        else:
            new_arg_i = self.args[i-1].reduce()
            if new_arg_i is not self.args[i-1]:
                result = self.copy()
                result.args[i-1] = new_arg_i
                if len(result.args) == 1 and isinstance(result, BindingOp):
                    reason = "Reduction of body"
                else:
                    reason = "Reduction of operand %s" % (i)
                return derived(result, self, desc=reason)
        return self

    def reduce_all(self):
        """Maximally reduce function-argument combinations in `self`."""
        # this is a dumb strategy: it's either not fully general (but I haven't found the case yet), or it's way
        # too inefficient, I'm not sure which; probably both.  The potential overkill is the recursive step.
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
                next_step = result.copy()
                next_step.args[i] = new_arg_i
                if len(result.args) == 1 and isinstance(result, BindingOp):
                    reason = "Recursive reduction of body"
                else:
                    reason = "Recursive reduction of operand %s" % (i+1)
                result = derived(next_step, result, desc=reason, subexpression=new_arg_i)
        if isinstance(result.op, TypedExpr):
            new_op = result.op.reduce_all()
            if new_op is not result.op:
                dirty = True
                next_step = result.copy()
                next_step.op = new_op
                result = derived(next_step, result, desc="Recursive reduction of operator", subexpression=new_op)
        self_dirty = False
        while result.reducible():
            new_result = result.reduce()
            if new_result is not result:
                dirty = True
                self_dirty = True
                result = new_result # no need to add a derivation here, reduce will do that already
            else:
                break # should never happen...but prevent loops in case of error
        if self_dirty:
            new_result = result.reduce_all() # TODO: is this overkill?
            result = new_result
        return result # could instead just do all the derivedness in one jump here




    def __call__(self, *args):
        """Attempt to construct a saturated version of self.  This constructs a composite TypedExpr, with the function (`self`) as
        the operator and the argument(s) as the arguments.  Type checking happens immediately."""
        
        #print("globals: ", globals())
        return TypedExpr.factory(self, *args)


    def __repr__(self):
        """Return a string representation of the TypedExpr.

        This is guaranteed (barring bugs) to produce a parsable string that builds the same object.
        """
        if not self.args:         # Constant or proposition with arity 0
            return repr(self.op)
        elif isinstance(self.op, LFun):
            return "(%s)(%s)" % (repr(self.op), ', '.join([repr(a) for a in self.args]))
        elif isinstance(self.op, TypedExpr) and self.op.type.functional():  # Functional or propositional operator
            arg_str = ', '.join([repr(a) for a in self.args])
            if isinstance(self.op, CustomTerm):
                return self.op.custom_appl(arg_str)
            elif isinstance(self.args[0], Tuple):
                # tuple already generates parens
                return '%s%s' % (repr(self.op), arg_str)
            else:
                return '%s(%s)' % (repr(self.op), arg_str)
        elif len(self.args) == 1: # Prefix operator
            return repr(self.op) + repr(self.args[0])
        else:                     # Infix operator
            return '(%s)' % (' '+self.op+' ').join([repr(a) for a in self.args])

    def latex_str(self):
        """Return a representation of the TypedExpr suitable for IPython Notebook display.

        In this case the output should be pure LaTeX."""
        if not self.args:
            return ensuremath(str(self.op))
        elif isinstance(self.op, LFun):
            return ensuremath("[%s](%s)" % (self.op.latex_str(), ', '.join([a.latex_str() for a in self.args])))
        elif isinstance(self.op, TypedExpr) and (self.op.type.functional()):  # Functional or propositional operator
            arg_str = ', '.join([a.latex_str() for a in self.args])
            if isinstance(self.op, CustomTerm):
                return ensuremath(self.op.custom_appl_latex(arg_str))
            elif isinstance(self.args[0], Tuple):
                # tuple already generates parens
                return ensuremath('%s%s' % (self.op.latex_str(), arg_str))
            else:
                return ensuremath('%s(%s)' % (self.op.latex_str(), arg_str))
        # past this point in the list of cases should only get hard-coded operators
        elif len(self.args) == 1: # Prefix operator
            return ensuremath(text_op_in_latex(self.op) + self.args[0].latex_str())
        else:                     # Infix operator
            return ensuremath('(%s)' % (' '+text_op_in_latex(self.op)+' ').join([a.latex_str() for a in self.args]))

    def _repr_latex_(self):
        return self.latex_str()

    def __str__(self):
        return "%s, type %s" % (self.__repr__(), self.type)

    def __eq__(self, other):
        """x and y are equal iff their ops and args are equal.

        Note that this is a _syntactic_ notion of equality, not a _semantic_ notion -- for example,
        two expressions would fail this notion of equality if one reduces to the other but that reduction
        has not been done.  Alphabetic variants will also not come out as equal."""
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

        Note that there are some special cases to worry about: ListedSets are not guaranteed to hash correctly.
        """
        # TODO: deal with ListedSets
        return hash(self.op) ^ hash(tuple(self.args))

    def __getitem__(self, i):
        """If `i` is a number, returns a part of `self` by index.  
        index 0 always gives the operator.
        index >=1 gives whatever arguments there are.  Note that this is shifted from the indexing of `self.args`.

        If `i` is a TypedExpr, try to construct an expression representing indexing."""
        if isinstance(i, TypedExpr):
            return TupleIndex(self, i)
        else:
            return ([self.op] + self.args).__getitem__(i)

    def __len__(self):
        """Return the number of parts of `self`, including the operator."""
        return len(self.args) + 1

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

class ApplicationExpr(TypedExpr):
    def __init__(self, fun, arg, defer=False, assignment=None):
        ts = get_type_system()
        fun = self.ensure_typed_expr(fun)
        arg = self.ensure_typed_expr(arg)

        history = False
        #self.derivation = None
        #self.type_guessed = False
        #self.defer = defer
        (f_type, a_type, out_type) = ts.unify_fa(fun.type, arg.type, type_env=assignment)
        if f_type is None:
            raise TypeMismatch(fun, arg, "Function argument combination (unification failed)")

        self.type = out_type
        if fun.type == f_type or defer:
            op = fun
        else:
            op = fun.try_adjust_type(f_type, derivation_reason="Function argument combination", assignment=assignment)
            history = True

        if a_type == arg.type or defer:
            args = [arg]
        else:
            args = [arg.try_adjust_type(a_type, derivation_reason="Function argument combination", assignment=assignment)]
            history = True
        super().__init__(op, *args, defer=defer)
        #self.op = op
        #self.args = args

        if history:
            # bit of a hack: build a derivation with the deferred version as the origin
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
        return ApplicationExpr(self.op, self.args[0], defer=self.defer)

    def local_copy(self, fun, arg):
        return ApplicationExpr(fun, arg, defer=self.defer)

class Tuple(TypedExpr):
    """TypedExpr wrapper on a tuple.

    This works basically as a python tuple would, and is indicated using commas within a parenthetical.
    `args` is a list containing the elements of the tuple."""
    def __init__(self, args, typ=None):
        # self.op = "Tuple"
        # self.derivation = None
        new_args = list()
        type_accum = list()
        for i in range(len(args)):
            if typ is None:
                a_i = self.ensure_typed_expr(args[i])
            else:
                a_i = self.ensure_typed_expr(args[i], typ=typ[i])
            new_args.append(a_i)
            type_accum.append(a_i.type)
        super().__init__("Tuple", *new_args)
        self.type = types.TupleType(*type_accum)

    def copy(self):
        return Tuple(self.args)

    def local_copy(self, op, *args):
        return Tuple(args, typ=self.type)

    def index(self, i):
        return self.args[i]

    def term(self):
        return False

    def tuple(self):
        """Return a python `tuple` version of the Tuple object."""
        return tuple(self.args)

    def __repr__(self):
        return "(" + ", ".join([repr(a) for a in self.args]) + ")"

    def latex_str(self, parens=True):
        inner = ", ".join([a.latex_str() for a in self.args])
        if parens:
            return ensuremath("(" + inner + ")")
        else:
            return ensuremath(inner)


# suppress any constant type
global suppress_constant_type
suppress_constant_type = False

# suppress only constant predicates
# a predicate type is either <e,t>, or any characteristic function of a set of tuples
global suppress_constant_predicate_type
suppress_constant_predicate_type = True

class TypedTerm(TypedExpr):
    """used for terms of arbitrary type.  Note that this is not exactly standard usage of 'term'.
    In general, these cover variables and constants.  The name of the term is 'op', and 'args' is empty.

    The attribute 'type_guessed' is flagged if the type was not specified; this may result in coercion as necessary."""
    def __init__(self, varname, typ=None, latex_op_str=None, assignment=None):
        # NOTE: does not call super
        self.op = num_or_str(varname)
        self.derivation = None
        self.defer = False
        update_a = False
        if assignment is not None:
            if self.op in assignment:
                ts = get_type_system()
                unified = ts.unify(typ, assignment[self.op].type)
                if unified is None:
                    raise TypeMismatch(self.term_factory(self.op, typ), assignment[self.op], "Failed to unify with type specified by assignment")
                else:
                    typ = unified
                    update_a = True
            else:
                update_a = True
        if typ is None:
            self.type = default_type(varname)
            self.type_guessed = True
        else:
            self.type_guessed = False
            self.type = typ
        if isinstance(self.op, Number): # this isn't very elegant...
            if self.type != type_n:
                raise TypeMismatch(self.op, self.type, "Numeric must have type n")
            self.type_guessed = False
        self.args = list()
        self.suppress_type = False
        self.latex_op_str = latex_op_str
        if update_a:
            assignment[self.op] = self

    def copy(self):
        return TypedTerm(self.op, typ=self.type)

    def local_copy(self, op):
        result = TypedTerm(op, latex_op_str = self.latex_op_str)
        result.type = self.type
        result.type_guessed = self.type_guessed
        return result

    def type_env(self, constants=False, target=None):
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

    def constant(self):
        """Return true iff `self` is a constant.

        This follows the prolog convention: a constant is a term with a capitalized first letter.  Numbers are constants."""
        return not is_var_symbol(self.op)

    def variable(self):
        """Return true iff `self` is a variable.

        This follows the prolog convention: a variable is a term with a lowercase first letter."""
        return is_var_symbol(self.op)

    def __repr__(self):
        return "%s_%s" % (self.op, repr(self.type))

    def should_show_type(self):
        if self.suppress_type:
            return False
        if suppress_constant_type and self.constant():
            return False
        if suppress_constant_predicate_type:
            if self.constant() and self.type.functional():
                if (self.type.left == types.type_e or isinstance(self.type.left, types.TupleType)) and self.type.right == types.type_t:
                    return False
        return True

    def try_coerce_new_argument(self, typ, remove_guessed = False, assignment=None):
        if not self.type_guessed:
            return None
        #self.type = self.type.add_internal_argument(typ)
        #coerced_op = TypedTerm(self.op, self.type.add_internal_argument(typ))
        coerced_op = self.copy()
        # TODO: not 100% sure this is right, and may lead to complications down the road
        coerced_op.type = self.type.add_internal_argument(typ)
        if not remove_guessed:
            coerced_op.type_guessed = True
        
        if assignment is not None and self.op in assignment:
            assignment[self.op] = coerced_op
        return coerced_op

    def latex_str(self):
        if self.latex_op_str is None:
            op = self.op
        else:
            op = self.latex_op_str
        if not self.should_show_type():
            return ensuremath("{%s}" % op)
        else:
            return ensuremath("{%s}_{%s}" % (op, self.type.latex_str()))

    def _repr_latex_(self):
        return self.latex_str()

class CustomTerm(TypedTerm):
    """A subclass of TypedTerm used for custom displays of term names.

    The main application is for English-like metalanguage a la Heim and Kratzer.  This isn't
    fully implemented as that metalanguage is actually extremely difficult to get right computationally..."""
    def __init__(self, varname, custom_english=None, suppress_type=True, small_caps=True, typ=None, assignment=None):
        TypedTerm.__init__(self, varname, typ=typ, assignment=assignment)
        self.custom = custom_english
        self.sc = small_caps
        self.suppress_type = suppress_type
        self.verbal = False
        # TODO: check type against custom string

    def copy(self):
        return CustomTerm(self.op, custom_english=self.custom, suppress_type=self.suppress_type, small_caps=self.sc, typ=self.type)

    def copy(self, op):
        return CustomTerm(op, custom_english=self.custom, suppress_type=self.suppress_type, small_caps=self.sc, typ=self.type)

    def latex_str(self):
        s = ""
        # custom made small caps
        if self.sc:
            if len(self.op) == 1:
                s += "{\\rm %s}" % (self.op[0].upper())
            else:
                s += "{\\rm %s {\\small %s}}" % (self.op[0].upper(), self.op[1:].upper())
        else:
            s += "{\\rm %s}" % self.op
        if not self.suppress_type:
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
            return "%s\\text{ }%s\\text{%s}" % (arg_str, self.latex_str(), self.get_custom())
        else:
            return "%s \\text{ %s }%s" % (arg_str, self.get_custom(), self.latex_str())

    def custom_appl(self, arg_str):
        if self.verbal:
            return "%s %s%s" % (arg_str, self.latex_str(), self.get_custom())
        else:
            return "%s %s %s" % (arg_str, repr(self), self.get_custom())


class MiniOp(object):
    """This is a class to pass to a TypeMismatch so that the operator is displayed nicely."""
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



class UnaryOpExpr(TypedExpr):
    """This class abstracts over expressions headed by specific unary operators.  It is not necessarily designed to be 
    instantiated directly, but rather subclassed for particular hard-coded operators.

    Because of the way the copy function works, it is currently not suited for direct instantiation.

    In logical terms, this corresponds to syncategorematic definitions of operators as is standard in definitions of logics.
    For example, statements like '~p is a sentence iff p is a sentence'.  While semantics is not currently implemented, it could be
    done in subclasses."""
    def __init__(self, typ, op, arg1, op_name_uni=None, op_name_latex=None):
        #self.derivation = None
        super().__init__(op, self.ensure_typed_expr(arg1, typ))
        #self.op = op
        # default behavior: type of body is type of whole
        #self.args = [self.ensure_typed_expr(arg1, typ)]
        self.type = typ
        if op_name_uni is None:
            self.op_name = op
        else:
            self.op_name = op_name_uni
        if op_name_latex is None:
            self.op_name_latex = op_name_uni
        else:
            self.op_name_latex = op_name_latex
        #self.type_constraints()

    def copy(self):
        """This must be overriden in classes that are not produced by the factory."""
        #return UnaryOpExpr(self.type, self.op, self.args[0], self.op_name, self.op_name_latex)
        return op_expr_factory(self.op, *self.args)

    def local_copy(self, op, *args):
        return op_expr_factory(self.op, *args)

    def type_constraints(self):
        # TODO: generalize somehow
        ts = get_type_system()
        unified = ts.unify(self.args[0].type, self.type)
        if unified is None:
            raise TypeMismatch(MiniOp.from_op(self), self.args[0], mode="Unary operator")
        if self.args[0].type != unified:
            if isinstance(self.args[0], TypedTerm):
                self.args[0] = self.args[0].copy()
                self.args[0].type = unified
            else:
                logger.warning("Unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.args[0].type, unified))

    def __str__(self):
        return "%s%s\nType: %s" % (self.op_name, repr(self.args[0]), self.type)

    def __repr__(self):
        return "%s%s" % (self.op_name, repr(self.args[0]))

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self):
        return ensuremath("%s %s" % (self.op_name_latex,  
                                                self.args[0].latex_str()))
    # TODO: if this is uncommented, it blocks inheritence of __hash__
    # will need to remember to fix hashing as well once I implement the TODO below.  (What are the rules?)
    #def __eq__(self, other):
    #    # TODO: implement equality up to alphabetic variants.
    #    # as is, alphabetic variants will not be equal.
    #    return super().__eq__(other)

class BinaryOpExpr(TypedExpr):
    """This class abstracts over expressions headed by specific binary operators.  It is not necessarily designed to be 
    instantiated directly, but rather subclassed for particular hard-coded operators.

    Because of the way the copy function works, it is currently not suited for direct instantiation at all."""
    def __init__(self, typ, op, arg1, arg2, op_name_uni=None, op_name_latex=None, tcheck_args=True):
        #self.derivation = None
        #self.op = op
        if tcheck_args:
            args = [self.ensure_typed_expr(arg1, typ), self.ensure_typed_expr(arg2, typ)]
        else:
            args = [self.ensure_typed_expr(arg1), self.ensure_typed_expr(arg2)]
        super().__init__(op, *args)
        self.type = typ
        if op_name_uni is None:
            self.op_name = op
        else:
            self.op_name = op_name_uni
        if op_name_latex is None:
            self.op_name_latex = op_name_uni
        else:
            self.op_name_latex = op_name_latex
        #self.type_constraints()

    #def copy(self):
    #    return BinaryOpExpr(self.type, self.op, self.args[0], self.args[1], self.op_name, self.op_name_latex)
    def copy(self):
        """This must be overriden by classes that are not produced by the factory."""
        #return UnaryOpExpr(self.type, self.op, self.args[0], self.op_name, self.op_name_latex)
        return op_expr_factory(self.op, *self.args)

    def local_copy(self, op, *args):
        return op_expr_factory(self.op, *args)

    def type_constraints(self):
        """Default behavior: types of arguments must match type of whole expression."""
        ts = get_type_system()
        if len(self.args) != 2 or not ts.eq_check(self.args[0].type, self.type)or not ts.eq_check(self.args[1].type, self.type):
            raise TypeMismatch(MiniOp.from_op(self), self.args, mode="Binary operator")

    def __str__(self):
        return "%s\nType: %s" % (repr(self), self.type)

    def __repr__(self):
        return "(%s %s %s)" % (repr(self.args[0]), self.op_name, repr(self.args[1]))

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self):
        return ensuremath("(%s %s %s)" % (self.args[0].latex_str(), self.op_name_latex,  
                                                self.args[1].latex_str()))

    @classmethod
    def join(cls, *l):
        """Joins an arbitrary number of arguments using the binary operator.  Note that currently association is left to right.
        Requires a subclass that defines a two-parameter __init__ function.  (I.e. will potentially fail if called on the abstract class.)

        Will also fail on operators that do not take the same type (i.e. SetContains).
        """
        if len(l) == 0:
            return true_term
        if len(l) == 1:
            return l[0]
        else:
            cur = l[0]
            for i in range(len(l) - 1):
                cur = cls(cur, l[i+1]) # will raise an error if the subclass doesn't define the constructor this way.
            return cur


    # TODO: if this is uncommented, it blocks inheritence of __hash__
    # will need to remember to fix hashing as well once I implement the TODO below.  (What are the rules?)
    #def __eq__(self, other):
    #    # TODO: implement equality up to alphabetic variants.
    #    # as is, alphabetic variants will not be equal.
    #    return super().__eq__(other)


# could make a factory function for these

class UnaryNegExpr(UnaryOpExpr): #unicode: ¬
    def __init__(self, body):
        super().__init__(type_t, "~", body, "~", "\\neg{}")

class BinaryAndExpr(BinaryOpExpr): #note: there is a unicode, ∧.
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "&", arg1, arg2, "&", "\\wedge{}")

class BinaryOrExpr(BinaryOpExpr): #unicode: ∨.
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "|", arg1, arg2, "|", "\\vee{}")

#unicode arrow: →
class BinaryArrowExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, ">>", arg1, arg2, ">>", "\\rightarrow{}")

# unicode: ↔
class BinaryBiarrowExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "<=>", arg1, arg2, "<=>", "\\leftrightarrow{}")

# TODO: generalize this?
class BinaryNeqExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        super().__init__(type_t, "^", arg1, arg2, "=/=", "\\not=")

class BinaryGenericEqExpr(BinaryOpExpr):
    """Type-generic equality.  This places no constraints on the type of `arg1` and `arg2` save that they be equal.  See `eq_factory`."""
    def __init__(self, arg1, arg2):
        arg1 = self.ensure_typed_expr(arg1)
        # maybe raise the exception directly?
        arg2 = self.ensure_typed_expr(arg2, arg1.type)
        # some problems with equality using '==', TODO recheck, but for now just use "<=>" in the normalized form
        super().__init__(type_t, "<=>", arg1, arg2, op_name_uni = "<=>", op_name_latex = "=", tcheck_args = False)

def eq_factory(arg1, arg2):
    """If type is type t, return a biconditional.  Otherwise, build an equality statement."""
    arg1 = TypedExpr.ensure_typed_expr(arg1)
    arg2 = TypedExpr.ensure_typed_expr(arg2)
    ts = get_type_system()
    if ts.eq_check(arg1.type, types.type_t):
        return BinaryBiarrowExpr(arg1, arg2)
    else:
        return BinaryGenericEqExpr(arg1, arg2)


def binary_num_op(op, op_uni=None, op_latex=None):
    """Factory for binary numeric operators."""
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            super().__init__(type_n, op, arg1, arg2, op_uni, op_latex)
    return BinOp

def binary_num_rel(op, op_uni=None, op_latex=None):
    """Factory for binary numeric relations."""
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            # this is a bit redundant but it works
            super().__init__(type_t, op, self.ensure_typed_expr(arg1, types.type_n), self.ensure_typed_expr(arg2, types.type_n), op_uni, op_latex, tcheck_args=False)
    return BinOp

BinaryLExpr = binary_num_rel("<", "<", "<")
BinaryLeqExpr = binary_num_rel("<=", "<=", "\\leq{}")
BinaryGeqExpr = binary_num_rel(">=", ">=", "\\geq{}")
BinaryGExpr = binary_num_rel(">", ">", ">")
BinaryPlusExpr = binary_num_op("+", "+", "+")
BinaryMinusExpr = binary_num_op("-", "-", "-")
BinaryDivExpr = binary_num_op("/", "/", "/")
BinaryTimesExpr = binary_num_op("*", "*", "*")
BinaryExpExpr = binary_num_op("**", "**", "**")


# There's only one of these, so a factory would be silly
class UnaryNegativeExpr(UnaryOpExpr):
    def __init__(self, body):
        super().__init__(type_n, "-", body, "-", "-")


class SetContains(BinaryOpExpr):
    """Binary relation of set membership.  This uses `<<` as the symbol.

    Note that this _does_ support reduction if the set describes its members by condition, 
    as set membership is equivalent to saturation of the characteristic function of the set."""
    def __init__(self, arg1, arg2):
        # seems like the best way to do the mutual type checking here?  Something more elegant?
        arg1 = self.ensure_typed_expr(arg1)
        arg2 = self.ensure_typed_expr(arg2, types.SetType(arg1.type))
        arg1 = self.ensure_typed_expr(arg1, arg2.type.content_type)
        #super().__init__(type_t, "<<", arg1, arg2, "∈", "\\in{}", tcheck_args=False)
        # was having some trouble with the ∈ symbol, not sure what the problem is but disabled for now.
        super().__init__(type_t, "<<", arg1, arg2, "<<", "\\in{}", tcheck_args=False)

    def copy(self):
        return SetContains(self.args[0], self.args[1])

    def local_copy(self, op, arg1, arg2):
        return SetContains(arg1, arg2)

    def reduce(self):
        if isinstance(self.args[1], ConditionSet):
            derivation = self.derivation
            step = (self.args[1].to_characteristic()(self.args[0])).reduce()
            step.derivation = derivation # suppress the intermediate parts of this derivation, if any
            return derived(step, self, "∈ reduction")
        else:
            # leave ListedSets as-is for now.  TODO could expand this using disjunction.
            return self

    def reducible(self):
        if isinstance(self.args[1], ConditionSet):
            return True
        return False


class TupleIndex(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        arg1 = self.ensure_typed_expr(arg1)
        if not isinstance(arg1.type, types.TupleType):
            raise types.TypeMismatch(arg1, arg2, mode="Tuple indexing (tuple required)")
        arg2 = self.ensure_typed_expr(arg2, types.type_n)
        if isinstance(arg2.op, Number): # TODO better way to determine whether arg2 is a constant of type type_n?
            if arg2.op >= len(arg1.type):
                raise TypeMismatch(arg1, arg2, mode="Index out of range for tuple type")
            output_type = arg1.type[arg2.op]
        else:
            output_type = types.VariableType("X") # TODO this is very problematic
            logger.warning("Using non-constant index; not well-supported at present.")
        super().__init__(output_type, "[]", arg1, arg2, "[]", "[]", tcheck_args=False)

    def copy(self):
        return TupleIndex(self.args[0], self.args[1])

    def local_copy(self, op, arg1, arg2):
        return TupleIndex(arg1, arg2)

    def __str__(self):
        return "%s\nType: %s" % (repr(self), self.type)

    def __repr__(self):
        return "(%s[%s])" % (repr(self.args[0]), repr(self.args[1]))

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self):
        return ensuremath("(%s[%s])" % (self.args[0].latex_str(), self.args[1].latex_str()))

    def reduce(self):
        if isinstance(self.args[0], Tuple) and isinstance(self.args[1].op, Number):
            result = self.args[0].tuple()[self.args[1].op].copy()
            return derived(result, self, "Resolution of index")
        else:
            return self


    def reducible(self):
        if isinstance(self.args[0], Tuple) and isinstance(self.args[1].op, Number):
            return True
        # no support for non-constant indices at present, not even ones that should be mathematically simplifiable
        return False


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

op_symbols = set(unary_symbols_to_op_exprs.keys()) | set(binary_symbols_to_op_exprs.keys())



# TODO raise exceptions
def op_expr_factory(op, *args):
    """Given some operator/relation symbol with arguments, construct an appropriate TypedExpr subclass for that operator."""
    # note that this conditional is necessary because the same symbol may involve both a unary and a binary operator
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
        raise ValueError("Too many arguments (%s) to operator '%s'" % (len(args), op))




class BindingOp(TypedExpr):
    """Abstract class for a unary operator with a body that binds a single variable in its body.

    Never instantiated directly.  To see how to use this, it may be helpful to look at the definite
    description tutorial, which shows how to build an iota operator."""

    binding_operators = dict()
    canonicalize_names = dict()
    unparsed_operators = set()
    op_regex = None
    init_op_regex = None

    # set the following in subclasses
    canonical_name = None
    secondary_names = set()
    op_name_uni = None
    op_name_latex = None

    def __init__(self, var_or_vtype, typ, body, varname=None, body_type = None, assignment=None):
        # NOTE: not calling superclass
        # Warning: can't assume in general that typ is not None.  I.e. may be set in subclass after a call
        # to this function.  Subclass is responsible for doing this properly...
        if body_type is None:
            body_type = typ
        if isinstance(var_or_vtype, str): # TODO: support type strings
            var_or_vtype = TypedExpr.term_factory(var_or_vtype)
        if isinstance(var_or_vtype, TypedTerm):
            if varname is not None:
                logger.warning("Overriding varname '%s' with '%s'" % (varname, var_or_vtype.op))
            self.varname = var_or_vtype.op
            self.vartype = var_or_vtype.type
        elif isinstance(var_or_vtype, types.TypeConstructor):
            if varname is None:
                varname = self.default_varname()
            self.varname = varname
            self.vartype = var_or_vtype
        else:
            raise NotImplementedError
        if not is_var_symbol(self.varname):
            raise ValueError("Need variable name (got '%s')" % self.varname)
        self.type = typ
        self.derivation = None
        self.type_guessed = False
        self.defer = False
        self.var_instance = TypedTerm(self.varname, self.vartype) # normalize class
        # set self.op so that hashing and equality comparison work correctly
        # TODO: consider overriding __eq__ and __hash__.
        self.op = "%s %s:" % (self.canonical_name, repr(self.var_instance))
        if assignment is None:
            assignment = {self.varname: self.var_instance}
            store_old_v = None
        else:
            #assignment = assignment.copy()
            if self.varname in assignment:
                store_old_v = assignment[self.varname]
            else:
                store_old_v = None
            assignment[self.varname] = self.var_instance
        #self.body = typed_expr(body)
        # TODO: this is sort of a mess here
        #print("BindingOp constructor L %s : %s" % (self.varname, repr(body)))
        self.args = [self.ensure_typed_expr(body, body_type, assignment=assignment)]
        #print("    args[0]: ", repr(self.args[0]))
        new_body = self.args[0].regularize_type_env(assignment) #, target={self.varname})
        #print("assignment in body: ", assignment)
        #print("    new_body: ", repr(new_body))
        new_body_env = new_body.type_env()
        #print(new_body_env)
        if self.varname in new_body_env: # binding can be vacuous
            if new_body_env[self.varname].type != self.vartype: # propagate type inference to binding expression
                self.vartype = new_body_env[self.varname].type
                self.var_instance = TypedTerm(self.varname, self.vartype)
                self.op = "%s %s:" % (self.canonical_name, repr(self.var_instance))
                self.args = [new_body]
                #print("    Using modified body")
        if store_old_v is not None:
            assignment[self.varname] = store_old_v

    def default_varname(self):
        return "x"

    @classmethod
    def add_op(cls, op):
        """Register an operator to be parsed."""
        if op.canonical_name is None:
            BindingOp.unparsed_operators.add(op)
        else:
            if op.canonical_name in BindingOp.binding_operators:
                logger.warning("Overriding existing binding operator '%s' in registry" % op.canonical_name)
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
        op_names = BindingOp.binding_operators.keys() | BindingOp.canonicalize_names
        # sort with longer strings first, to avoid matching subsets of long names
        # i.e. | is not greedy, need to work around that.
        op_names = list(op_names)
        op_names.sort(reverse=True)
        if len(op_names) == 0:
            BindingOp.op_regex = None
            BindingOp.init_op_regex = None
        else:
            regex = "(" + ("|".join(op_names)) + ")"
            BindingOp.op_regex = re.compile(regex)
            BindingOp.init_op_regex = re.compile("^\s*" + regex)

    @property
    def body(self):
        return self.args[0]

    def copy(self):
        # implement in subclass
        raise NotImplementedError

    def local_copy(self):
        raise NotImplementedError

    def alpha_convert(self, new_varname):
        """Produce an alphabetic variant of the expression w.r.t. the bound variable, with new_varname as the new name.

        Returns a copy.  Will not affect types of either the expression or the variables."""
        new_self = self.copy()
        new_self.args[0] = variable_convert(self.args[0], {self.varname: new_varname})
        new_self.varname = new_varname
        return new_self

    def latex_op_str(self):
        return self.latex_op_str_short()

    def latex_op_str_short(self):
        return "%s %s_{%s} \\: . \\:" % (self.op_name_latex, 
                                                self.varname, 
                                                self.vartype.latex_str())

    def __str__(self):
        return "%s %s : %s, Type: %s" % (self.op_name, self.varname, repr(self.body), self.type)

    def latex_str_long(self):
        return self.latex_str() + "\\\\ Type: %s" % self.type.latex_str()

    def latex_str(self):
        return ensuremath("%s %s" % (self.latex_op_str(),  
                                                self.body.latex_str()))
    # TODO: if this is uncommented, it blocks inheritence of __hash__
    # will need to remember to fix hashing as well once I implement the TODO below.  (What are the rules?)
    #def __eq__(self, other):
    #    # TODO: implement equality up to alphabetic variants.
    #    # as is, alphabetic variants will not be equal.
    #    return super().__eq__(other)

    def __repr__(self):
        return "(%s %s: %s)" % (self.op_name, repr(self.var_instance), repr(self.body))

    @property
    def op_name(self):
        if self.op_name_uni is not None and self.op_name_uni in self.secondary_names:
            return self.op_name_uni
        else:
            return self.canonical_name


    def free_variables(self):
        return super().free_variables() - {self.varname}

    def bound_variables(self):
        return super().bound_variables() | {self.varname}

    def type_env(self, constants=False, target=None):
        sub_env = self.args[0].type_env(constants=constants, target=target)
        if self.varname in sub_env: # binding can be vacuous
            del sub_env[self.varname]
        return sub_env

    def vacuous(self):
        """Return true just in case the operator's variable is not free in the body expression."""
        return self.varname in super().free_variables()

    def term(self):
        return False

    @classmethod
    def try_parse_header(cls, s, assignment=None, locals=None):
        """Try and parse the header of a binding operator expression, i.e. everything up to the body including ':'.
        If this succeeds, it will return a tuple with the class object, the variable name, the variable type, and the string after the ':'' if any.
        If it fails, it will either return None or raise an exception.  That exception is typically a ParseError.
        """

        i = 0
        if BindingOp.init_op_regex is None:
            return None # no operators to parse
        op_match = re.match(BindingOp.init_op_regex, s)
        if not op_match:
            raise parsing.ParseError("Unknown operator when trying to parsing binding operator expression", s, None, met_preconditions=False)
        op_name = op_match.group(1) # operator name
        #i += len(op_name)
        i = op_match.end(1)

        if op_name in BindingOp.canonicalize_names:
            op_name = BindingOp.canonicalize_names[op_name]
        if op_name not in BindingOp.binding_operators:
            raise Error("Can't find binding operator '%s'; should be impossible" % op_name)
        op_class = BindingOp.binding_operators[op_name]

        split = s.split(":", 1)
        if (len(split) != 2):
            # possibly should change to met_preconditions = True in the future.  At this point, we have seen a binding expression token.
            raise parsing.ParseError("Missing ':' in binding operator expression", s, None, met_preconditions=False)
        header, remainder = split
        vname = header[i:].strip() # should remove everything but a variable name
        (v, t) = cls.try_parse_typed_term(vname, strict=True)
        if not is_var_symbol(v):
            raise parsing.ParseError("Need variable name in binding operator expression (received '%s')" % v, s, None)
        if t is None:
            # TODO: flag as a guessed type somehow?
            t = default_variable_type(v)
        return (op_class, v, t, remainder)

    @classmethod
    def try_parse_binding_struc_r(cls, struc, assignment=None, locals=None, vprefix="ilnb"):
        """Attempt to parse structure `s` as a binding structure.  Used by the factory function.
        assignment: a variable assignment to use when parsing.

        `struc` is a semi-AST with all parenthetical structures parsed.  (See `parsing.parse_paren_str`.)

        Format: 'Op v : b'
          * 'Op' is one of 'lambda', 'L', 'λ', 'Forall', 'Exists', 'Iota'.  (Subclasses can register themselves to be parsed.)
          * 'v' is a variable name expression (see try_parse_typed_term), e.g. 'x_e'
          * 'b' is a function body, i.e. something parseable into a TypedExpr.

        If 'v' does not provide a type, it will attempt to guess one based on the variable name.
        The body will be parsed using a call to the recursive `TypedExpr.try_parse_paren_struc_r`, with a shifted assignment using the new variable 'v'.

        Returns a subclass of BindingOp.
        """
        #print(struc)

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
        (op_class, v, t, remainder) = result
        # remainder is any string left over from parsing the header.
        if bracketed:
            # note: syntax checking for bracket matching is already done, this does not need to check for that here.
            assert(parsing.brackets[struc[0]] == struc[-1])
            new_struc = [remainder,] + struc[2:-1]
        else:
            new_struc = [remainder,] + struc[1:]
        #print(new_struc)
        if assignment is None: 
            assignment = dict()
        if v in assignment:
            store_old_v = assignment[v]
        else:
            # create a new one to avoid side effects
            #assignment = dict(assignment)
            store_old_v = None
        assignment[v] = TypedTerm(v, t)
        body = None
        try:
            body = TypedExpr.try_parse_paren_struc_r(new_struc, assignment=assignment, locals=locals, vprefix=vprefix)
            #print("a: ", assignment, body.__class__)
        except Exception as e:
            if isinstance(e, parsing.ParseError):
                raise e
            else:
                raise parsing.ParseError("Binding operator expression has unparsable body", parsing.flatten_paren_struc(struc), None, e=e)
        if body is None:
            raise parsing.ParseError("Can't create body-less binding operator expression", parsing.flatten_paren_struc(struc), None)
        #print("a: ", assignment, op_class)
        result = op_class(var_or_vtype=t, varname=v, body=body, assignment=assignment)
        if store_old_v is not None:
            assignment[v] = store_old_v
        else:
            del assignment[v]
        return result

class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""

    canonical_name = "Set"
    op_name_uni="Set"
    op_name_latex="Set"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body, varname=varname, body_type=types.type_t, assignment=assignment)
        self.type = types.SetType(self.vartype)

    def copy(self):
        return ConditionSet(self.vartype, self.body, self.varname)

    def local_copy(self, op, arg):
        return ConditionSet(self.vartype, arg, self.varname)

    def structural_singleton(self):
        pass

    def term(self):
        return False

    #def __repr__(self):
    #    return "{%s | " % self.varname + repr(self.body) + "}"

    def latex_str(self, parens=True):
        return ensuremath("\{%s_{%s}\:|\: " % (self.varname, self.vartype.latex_str()) + self.body.latex_str() + "\}")

    def __lshift__(self, i):
        return SetContains(i, self)

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname)

    def try_adjust_type(self, new_type, derivation_reason=None, assignment=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unified = ts.unify(new_type, self.type)
        if unified is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unified:
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            inner_type = unified.content_type
            char = self.to_characteristic()
            sub_var = TypedTerm(self.varname, inner_type)
            new_condition = char.apply(sub_var, assignment=assignment)
            return derived(ConditionSet(inner_type, new_condition, self.varname), self, derivation_reason)

BindingOp.add_op(ConditionSet)

class ListedSet(TypedExpr):
    """A listed set is a set that simply lists members.

    _NOTE_: order is not guaranteed to be stable in a ListedSet, which may create all sorts of issues."""
    canonical_name = "ListedSet"
    op_name_uni="ListedSet"
    op_name_latex="ListedSet"

    def __init__(self, iterable, typ=None, assignment=None):
        s = set(iterable) # just make it a set first, remove duplicates, flatten order
        args = [self.ensure_typed_expr(a,assignment=assignment) for a in s]
        if len(self.args) == 0 and typ is None:
            typ = types.VariableType("X") # could be a set of anything
        elif typ is None:
            typ = self.args[0].type
        for i in range(len(self.args)): # type checking TODO: this isn't right, would need to pick the strongest type
            args[i] = self.ensure_typed_expr(self.args[i], typ)
        super().__init__("Set", *args)
        #self.op = "Set"
        self.type = types.SetType(typ)

    def subst(self, i, s):
        if len(self.args) < 2:
            return super().subst(i, s)
        else:
            raise NotImplementedError("Beta reduction into a set of size > 1 not currently supported.") # TODO deal with this
            # the problem is the same as usual -- set order isn't stable so we need to do this all at once rather than 
            # member-by-member.

    def copy(self):
        return ListedSet(self.args)

    def local_copy(self, op, *args):
        return ListedSet(args)

    def term(self):
        return False

    def __lshift__(self, i):
        """Use the `<<` operator for set membership."""
        return SetContains(i, self)

    def set(self):
        """Return a python `set` version of the ListedSet.

        Note that this isn't guaranteed to be defined for anything with a set type."""
        return set(self.args)

    def cardinality(self):
        return len(self.args)

    def to_condition_set(self):
        """Convert to a condition set by disjoining members."""
        # ensure that we build a condition set from a variable that is not free in any of the members
        varname = self.find_safe_variable(starting="x")
        conditions = [BinaryGenericEqExpr(TypedTerm(varname, a.type), a) for a in self.args]
        return ConditionSet(self.type.content_type, BinaryOrExpr.join(*conditions), varname=varname)

    def reduce_all(self):
        """Special-cased reduce_all for listed sets.  There are two problems.  First, the reduction 
        may actually result in a change in the size of the set, something generally not true of 
        reduction elsewhere.  Second, because the constructor calls `set`, `copy` is not guaranteed
        to return an object with a stable order.  Therefore we must batch the reductions (where the 
        TypedExpr version doesn't).

        Note that currently this produces non-ideal derivation sequences."""
        dirty = False
        accum = list()
        result = self
        for i in range(len(result.args)):
            new_arg_i = result.args[i].reduce_all()
            if new_arg_i is not result.args[i]:
                dirty = True
                reason = "Recursive reduction of set member %s" % (i+1)
                # TODO: this isn't quite right but I can't see what else to do right now
                result = derived(result, result, desc=reason, subexpression=new_arg_i, allow_trivial=True)
                accum.append(new_arg_i)
            else:
                accum.append(new_arg_i)
        if dirty:
            new_result = ListedSet(accum)
            new_result = derived(new_result, result, desc="Construction of set from reduced set members")
            result = new_result
        return result


    def __repr__(self):
        #return "ListedSet : " + repr(tuple(self.args))
        return repr(set(self.args))

    def latex_str(self):
        inner = ", ".join([a.latex_str() for a in self.args])
        return ensuremath("\{" + inner + "\}")

    def try_adjust_type(self, new_type, derivation_reason=None, assignment=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unified = ts.unify(new_type, self.type)
        if unified is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unified:
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            inner_type = unified.content_type
            content = [a.try_adjust_type(inner_type, derivation_reason=derivation_reason, assignment=assignment) for a in self.args]
            return derived(ListedSet(content), self, derivation_reason)

#BindingOp.add_op(ListedSet)

class ForallUnary(BindingOp):
    """Universal unary quantifier"""
    canonical_name = "Forall"
    op_name_uni = "∀"
    op_name_latex = "\\forall{}"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype, types.type_t, body, varname=varname, assignment=assignment)

    def copy(self):
        return ForallUnary(self.vartype, self.body, self.varname)

    def local_copy(self, op, arg):
        return ForallUnary(self.vartype, arg, self.varname)

BindingOp.add_op(ForallUnary)

class ExistsUnary(BindingOp):
    """Existential unary quantifier"""
    canonical_name = "Exists"
    op_name_uni="∃"
    op_name_latex="\\exists{}"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype, types.type_t, body, varname=varname, assignment=assignment)

    def copy(self):
        return ExistsUnary(self.vartype, self.body, self.varname)

    def local_copy(self, op, arg):
        return ExistsUnary(self.vartype, arg, self.varname)        

BindingOp.add_op(ExistsUnary)

class IotaUnary(BindingOp):
    """Iota operator.  Note that this is purely syntactic, no presuppositions or model constraints implemented."""
    canonical_name = "Iota"
    op_name_uni = "ι"
    op_name_latex="\\iota{}"
    secondary_names = {"ι"}

    def __init__(self, var_or_vtype, body, varname=None, assignment=None):
        body = self.ensure_typed_expr(body, assignment=assignment)
        #if body.type != types.type_t:
        #    raise TypeMismatch
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body, varname=varname, body_type=types.type_t, assignment=assignment)
        self.type = self.vartype

    def copy(self):
        return IotaUnary(self.vartype, self.body, self.varname)

    def local_copy(self, op, arg):
        return IotaUnary(self.vartype, arg, self.varname)        


BindingOp.add_op(IotaUnary)

class LFun(BindingOp):
    """A typed function.  Can itself be used as an operator in a TypedExpr.

    """
    canonical_name = "Lambda"
    secondary_names = {"L", "λ", "lambda"}
    op_name_uni="λ"
    op_name_latex="\\lambda{}"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None):
        #print("a: ", assignment, body.__class__)
        body = self.ensure_typed_expr(body, assignment=assignment)
        # Use placeholder typ argument of None.  This is because the input type won't be known until
        # the var_or_vtype argument is parsed, which is done in the superclass constructor.
        # sort of a hack, this could potentially cause odd side effects if BindingOp.__init__ is changed without
        # taking this into account.
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body, varname=varname, body_type=body.type, assignment=assignment)
        self.type = FunType(self.vartype, body.type)

    @property
    def argtype(self):
        return self.type.left

    @property
    def returntype(self):
        return self.type.right

    def copy(self):
        return LFun(self.argtype, self.body, self.varname)

    def local_copy(self, op, arg):
        return LFun(self.argtype, arg, self.varname)

    def try_adjust_type(self, new_type, derivation_reason=None, assignment=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unified = ts.unify(new_type, self.type)
        if unified is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unified:
            return self
        else: # either input or output type can be strengthened
            #new_body = self.body.try_adjust_type(unify_a.right) # will only make copy if necessary
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            new_argtype = unified.left
            if self.argtype != unified.left:
                # arg type needs to be adjusted, and hence all instances of the bound variable as well.  Do this with beta reduction.
                new_var = TypedTerm(self.varname, unified.left)
                new_body = self.apply(new_var)
            else:
                new_body = self.body
            #if new_body.type != unify_a.right:
            new_body = new_body.try_adjust_type(unified.right, derivation_reason=derivation_reason, assignment=assignment) # will only make copy if necessary
            new_fun = LFun(new_argtype, new_body, self.varname)
            return derived(new_fun, self, derivation_reason)
        

    def apply(self,arg):
        """Apply an argument directly to the function.

        `__call__` plus `reduce` is (almost) equivalent to `apply`, but using `apply` directly will not generate a derivations."""
        # do I really want flexible equality here??
        # TODO: return to this.  Right now a type mismatch still gets raised during beta reduction.
        ts = get_type_system()
        if ts.eq_check(self.argtype, arg.type):
            # first check for potential variable name collisions when substituting, and the substitute
            #TODO: do I want to actually return the result of alpha converting?  May be needed later?
            new_self = alpha_convert(self, unsafe_variables(self, arg))
            # TODO: the copy here is a hack.  Right now identity functions result in no copying at all, leading to very
            # wrong results.  This needs to be tracked down to its root and fixed.
            return (beta_reduce_ts(new_self.body, new_self.varname, arg)).copy()
            #return beta_reduce_ts(self.body, self.varname, alpha_convert(arg, unsafe_variables(self, arg)))
        else:
            raise TypeMismatch(self,arg, "Application")

    # def __call__(self, *args):
    #     """Create a new expression that is the result of applying arg to the function

    #     call + reduce is (almost) equivalent to apply; the difference is that `apply` will not generate a derivation."""
    #     #print(locals())
    #     return TypedExpr.factory(self, *args)

    def compose(self, other):
        """Function composition."""
        return fun_compose(self, other)

    def __mul__(self, other):
        """Override `*` as function composition for LFuns.  Note that this _only_ works for LFuns currently, not functional constants/variables."""
        return self.compose(other)

def geach_combinator(gtype, ftype):
    body = term("g", gtype)(term("f", ftype)(term("x", ftype.left)))
    combinator = LFun(gtype, LFun(ftype, LFun(ftype.left, body,varname="x"),varname="f"), varname="g")
    return combinator

def fun_compose(g, f):
    """Function composition using the geach combinator for the appropriate type, defined above."""
    if (not (g.type.functional() and f.type.functional()
             and g.type.left == f.type.right)):
        raise types.TypeMismatch(g, f, "Function composition")
    combinator = geach_combinator(g.type, f.type)
    result = (combinator(g)(f)).reduce_all()
    return result



BindingOp.add_op(LFun)

def unsafe_variables(fun, arg):
    """For a function and an argument, return the set of variables that are not safe to use in application."""
    return arg.free_variables() & fun.body.bound_variables()

def beta_reduce_ts(t, varname, s):
    if not is_var_symbol(varname):
        raise ValueError("Beta reduction passed non-variable '%s'" % varname)
    if varname in t.free_variables():
        subst = TypedExpr.ensure_typed_expr(s)            
        ts = get_type_system()
        #print("asdf %s, %s" % (varname, repr(t)))
        if (t.term() and t.op == varname):
            if not ts.eq_check(t.type,subst.type):
                raise TypeMismatch(t, subst, "Beta reduction") # TODO make less cryptic
            #print("substituting with %s" % subst)
            return subst # TODO copy??
        # we will be changing something in this expression, but not at this level of recursion, so make a copy.
        # TODO: use local_copy
        t = t.copy()
        if isinstance(t.op, TypedExpr):
            # operator is a possibly complex TypedExpr
            new_op = beta_reduce_ts(t.op, varname, subst)
            t = t.subst(0, new_op)
        for i in range(len(t.args)):
            assert(isinstance(t.args[i], TypedExpr))
            new_arg_i = beta_reduce_ts(t.args[i], varname, subst)
            t = t.subst(i+1, new_arg_i)
        #print("beta reduce returning %s" % t.args)
    return t

def variable_replace(expr, m):
    def transform(e):
        return TypedExpr.factory(m[e.op])
    return variable_transform(expr, m.keys(), transform)

def variable_replace_strict(expr, m):
    def transform(e):
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            raise TypeMismatch(e, result, "Variable replace (strict types)")
        return result
    return variable_transform(expr, m.keys(), transform)

def variable_replace_unify(expr, m):
    def transform(e):
        ts = get_type_system()
        result = TypedExpr.factory(m[e.op])
        if result.type != e.type:
            unify = ts.unify(result.type, e.type)
            if unify is None:
                raise TypeMismatch(e, result, "Variable replace (unify failed)")
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

                #print("replacing %s with %s type %s (%s in %s)" % (repr(e), repr(result), unify, m, expr))
                #print(result.type, e.type)
        else:
            if result.term() and result.op == e.op:
                return e
            else:
                return result

    r = variable_transform_rebuild(expr, m.keys(), transform)
    #print("        transform to: ", repr(r))
    return r
    #return variable_transform(expr, m.keys(), transform)

def variable_convert(expr, m):
    def transform(e):
        return TypedTerm(m[e.op], e.type)
    return variable_transform(expr, m.keys(), transform)

def variable_transform(expr, dom, fun):
    """Transform free instances of variables in expr, as determined by the function fun.

    Operates on a copy.
    expr: a TypedExpr
    dom: a set of variable names
    fun: a function from terms to TypedExprs."""
    # TODO: check for properly named variables?
    # TODO: double check -- what if I recurse into a region where a variable becomes free again??  I think this goes wrong
    targets = dom & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be transformed.
            return fun(expr)
        expr = expr.copy()
        if isinstance(expr.op, TypedExpr):
            expr.op = variable_transform(expr.op, dom, fun)
        for i in range(len(expr.args)):
            if isinstance(expr.args[i], TypedExpr):
                expr.args[i] = variable_transform(expr.args[i], dom, fun)
            else:
                # ???
                raise ValueError("problem during variable conversion...") # TODO: make less cryptic
    return expr

def variable_transform_rebuild(expr, dom, fun):
    """Transform free instances of variables in expr, as determined by the function fun.

    Operates on a copy.
    expr: a TypedExpr
    dom: a set of variable names
    fun: a function from terms to TypedExprs."""
    # TODO: check for properly named variables?
    # TODO: double check -- what if I recurse into a region where a variable becomes free again??  I think this goes wrong
    targets = dom & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be transformed.
            #print("transforming %s to %s" % (expr, fun(expr)))
            return fun(expr)
        #expr = expr.copy()
        seq = list()
        dirty = False
        if isinstance(expr.op, TypedExpr):
            new_op = variable_transform_rebuild(expr.op, dom, fun)
            if new_op != expr.op:
                dirty = True
            seq.append(new_op)
        else:
            seq.append(expr.op)
        for i in range(len(expr.args)):
            if isinstance(expr.args[i], TypedExpr):
                #expr.args[i] = variable_transform(expr.args[i], dom, fun)
                seq.append(variable_transform_rebuild(expr.args[i], dom, fun))
                if seq[-1] != expr.args[i]:
                    dirty = True
                #print("transforming %s to %s" % (expr.args[i], seq[-1]))
            else:
                # ???
                raise ValueError("problem during variable conversion...") # TODO: make less cryptic
        if dirty:
            #print("            local_copy of %s" % repr(expr))
            expr = expr.local_copy(*seq)
    return expr

#def try_adjust_variable_type(expr, typ, varname):
#    def transform(e):
#        return TypedTerm(varname, typ)


# TODO: these last two functions are very similar, make an abstracted version?

def alpha_variant(x, blockset):
    """find a simple variant of string x that isn't in blocklist.  Try adding numbers to the end, basically.
    side effect WARNING: updates blocklist itself to include the new variable."""
    if not x in blockset:
        return x
    split = utils.vname_split(x)
    if len(split[1]) == 0:
        count = 1
    else:
        count = int(split[1]) + 1 # TODO: double check this -- supposed to prevent counterintuitive thing like blocked "a01" resulting in "a1"
    prefix = split[0]
    t = prefix + str(count)
    while t in blockset:
        count += 1
        t = prefix + str(count)
    blockset.add(t) # note: fails for non-sets
    return t

def alpha_convert(t, blocklist):
    """ produce an alphabetic variant of t that is guaranteed not to have any variables in blocklist.  

    Possibly will not change t."""
    overlap = t.bound_variables() & blocklist
    full_bl = blocklist | t.free_variables() | t.bound_variables()
    # note that this relies on the side effect of alpha_variant...
    conversions = {x : alpha_variant(x, full_bl) for x in overlap}
    return alpha_convert_r(t, overlap, conversions)

def alpha_convert_r(t, overlap, conversions):
    overlap = overlap & t.bound_variables()
    if overlap:
        # can safely make a copy, because there will be a change in there somewhere
        if isinstance(t, BindingOp):
            if t.varname in overlap:
                # the operator is binding variables in the overlap set.
                # rename instances of this variable that are free in the body of the operator expression.
                t = t.alpha_convert(conversions[t.varname])
            else:
                t = t.copy()
        else:
            t = t.copy()
        if isinstance(t.op, TypedExpr):
            t.op = alpha_convert_r(t.op, overlap, conversions)
        for i in range(len(t.args)):
            t.args[i] = alpha_convert_r(t.args[i], overlap, conversions)
    return t

global true_term, false_term
true_term = TypedTerm("True", types.type_t)
false_term = TypedTerm("False", types.type_t)

def test_setup():
    global ident, ia, ib, P, Q, p, y, t, testf, body, pmw_test1, pmw_test1b, t2
    ident = LFun(type_e, "x", "x")
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
    # test: when a free variable in a function scopes under an operator, do not bind the variable on application
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
            #return undetermined_type
    else:
        # TODO: more default special cases?  predicates?
        raise NotImplementedError

def typed_expr(s):
    # class method replaces this.  Call this instead of factory, which has a 
    # slightly different semantics -- factory will make a copy if handed a TypedExpr.
    return TypedExpr.ensure_typed_expr(s)

def is_symbol(s):
    "A string s is a symbol if it starts with an alphabetic char."
    return isinstance(s, str) and len(s) > 0 and s[:1].isalpha() and not is_multiword(s)

def is_var_symbol(s):
    "A logic variable symbol is an initial-lowercase string."
    return is_symbol(s) and s[0].islower()

def is_prop_symbol(s):
    """A proposition logic symbol is an initial-uppercase string other than
    TRUE or FALSE."""
    return is_symbol(s) and s[0].isupper() and s != 'TRUE' and s != 'FALSE'

def is_multiword(s):
    """a string is multiword if there is intermediate (non-initial and non-trailing) whitespace."""
    #TODO this could be more efficient
    return (len(s.strip().split()) != 1)

def variables(s):
    """Return a set of the variables in expression s.
    >>> ppset(variables(F(x, A, y)))
    set([x, y])
    >>> ppset(variables(F(G(x), z)))
    set([x, z])
    >>> ppset(variables(expr('F(x, x) & G(x, y) & H(y, z) & R(A, z, z)')))
    set([x, y, z])
    """
    result = set([])
    def walk(s):
        if is_variable(s):
            result.add(s)
        else:
            for arg in s.args:
                walk(arg)
    walk(s)
    return result

class DerivationStep(object):
    """A single step of a derivation."""
    def __init__(self, result,  desc=None, origin=None, latex_desc=None, subexpression=None, trivial=False):
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
                return ensuremath("(" + (" + ".join([o.latex_str() for o in self.origin])) + ")")
            else:
                return "(" + (" + ".join([repr(o) for o in self.origin])) + ")"

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
            for i in range(len(self.steps)): # assume that origin matches previous result.  Could check this.
                if self.steps[i].trivial and ignore_trivial:
                    continue
                if latex:
                    if self.steps[i].trivial:
                        l.append(("...", self.steps[i].latex_desc, self.steps[i].subexpression))
                    else:
                        l.append((self.steps[i].result.latex_str(), self.steps[i].latex_desc, self.steps[i].subexpression))
                else:
                    l.append((repr(self.steps[i].result), self.steps[i].desc, self.steps[i].subexpression))
        return l

    def latex_steps_str(self, recurse=False):
        l = self.steps_sequence(latex=True)
        s = "<table>"
        i = 1
        bare_tr = "<tr>"
        uline_tr = "<tr style=\"border-bottom:1px solid #848482\">"
        for (expr, reason, subexpression) in l:
            if reason is None:
                reason_str = ""
            else:
                reason_str = "<span style=\"color:blue\">%s</span>" % reason

            if recurse and subexpression and subexpression.derivation:
                s += "%s<td style=\"padding-right:5px;vertical-align:bottom\"></td><td style=\"padding-right:5px;vertical-align:bottom\"></td><td style=\"padding-left:10px;border-left:1px solid #848482\">%s</td></tr>" % (bare_tr, reason_str)
                s += "%s<td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td><td style=\"padding-right:5px;vertical-align:bottom\">%s</td><td style=\"padding-left:10px;border-left:1px solid #848482;padding-bottom:3px\">%s</td></tr>" % (uline_tr, i, expr, subexpression.derivation.latex_steps_str(recurse=True))

            else:
                s += "%s<td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td><td style=\"padding-right:5px;vertical-align:bottom\">%s</td><td style=\"padding-left:10px;border-left:1px solid #848482\">%s</td></tr>" % (uline_tr, i, expr, reason_str)
            i += 1
        s += "</table>"
        return s

    def build_display_tree(self, recurse=False, parent=None, reason=None, style=None):
        defaultstyle = display.lr_table_style
        style = display.Styled.merge_styles(style, defaultstyle)
        l = self.steps_sequence(latex=True)
        parts = list()
        for (expr, subreason, subexpression) in l:
            if reason == "":
                reason = None
            if subexpression and subexpression.derivation and (recurse):
                parts.append(subexpression.derivation.build_display_tree(recurse=recurse, parent=expr, reason=subreason, style=style))
            else:
                parts.append(display.RecursiveDerivationDisplay(expr, explanation=subreason, parts=None, style=style))
        if len(parts) == 0:
            parts = None
        return display.RecursiveDerivationDisplay(parent, explanation=reason, parts=parts, style=style)

    def trace(self, recurse=True, style=None):
        #return MiniLatex(self.latex_steps_str(recurse=recurse))
        return self.build_display_tree(recurse=recurse, style=style)

    def show(self, recurse=False, style=None):
        return self.trace(recurse=recurse, style=style)

    def _repr_latex_(self):
        #return self.latex_steps_str()
        return self.build_display_tree(recurse=False)._repr_latex_()

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

    def __str__(self):
        return self.steps_str()


def derivation_factory(result, desc=None, latex_desc=None, origin=None, steps=None, subexpression=None, trivial=False):
    """Factory function for `Derivation`s.  See `derived`."""
    if origin is None:
        if steps is not None and len(steps) > 0:
            origin = steps[-1].result
    drv = Derivation(steps)
    # note: will make a copy of the derivation if steps is one; may be better to have something more efficient in the long run
    drv.add_step(DerivationStep(result, desc=desc, origin=origin, latex_desc=latex_desc, subexpression=subexpression, trivial=trivial))
    return drv

def derived(result, origin, desc=None, latex_desc=None, subexpression=None, allow_trivial=False):
    """Convenience function to return a derived TypedExpr while adding a derivational step.
    Always return result, adds or updates its derivational history as a side effect."""
    trivial = False
    if result == origin: # may be inefficient?
        if allow_trivial:
            trivial = True
        else:
            return result
    if result.derivation is None:
        d = origin.derivation
    else:
        d = result.derivation
    result.derivation = derivation_factory(result, desc=desc, latex_desc=latex_desc, origin=origin, steps=d, subexpression=subexpression, trivial=trivial)
    return result



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
    result = te(repr(e))
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

def random_term(typ, blockset=None, usedset=set(), prob_used=0.8, prob_var=0.5):
    if blockset is None:
        blockset = set()
    is_var = True
    if random.random() > prob_var:
        is_var = False
    # need to first filter to see if there is a possible used term.  Decide whether we're generating
    # a variable first so that this can be part of the filter.
    used_typed = [x for x in list(usedset) if (x.type==typ and x.variable() == is_var)]
    if random.random() < prob_used and len(used_typed) > 0:
        varname = (random.choice(list(used_typed))).op
    else:
        if typ in random_term_base.keys():
            base = random_term_base[typ]
        else:
            base = "f"
        if not is_var:
            base = base.upper()
        varname = alpha_variant(base, blockset | {n.op for n in usedset})
    return TypedExpr.term_factory(varname, typ)

def random_fa_combo(output_type, ctrl, max_type_depth=1):
    ts = get_type_system()
    input_type = ts.random_type(max_type_depth, 0.5, allow_variables=False)
    fun_type = types.FunType(input_type, output_type)
    result = (ctrl(typ=fun_type))(ctrl(typ=input_type))
    return result

def random_lfun(typ, ctrl):
    global random_used_vars
    input_type = typ.left
    body_type = typ.right
    variable = random_term(input_type, usedset=random_used_vars, prob_used=0.2, prob_var=1.0)
    random_used_vars |= {variable}
    return LFun(variable, ctrl(typ=body_type))

def random_binding_expr(ctrl, max_type_depth=1):
    global random_used_vars
    ts = get_type_system()
    options = [ForallUnary, ExistsUnary]
    op_class = random.choice(options)
    var_type = ts.random_type(max_type_depth, 0.5)
    variable = random_term(var_type, usedset=random_used_vars, prob_used=0.2, prob_var=1.0)
    random_used_vars |= {variable}
    return op_class(variable, ctrl(typ=type_t))

# ugh, need to find a way to do this not by side effect
global random_used_vars
random_used_vars = set()

def random_expr(typ=None, depth=1, used_vars=None):
    """Generate a random expression of the specified type `typ`, with an AST of specified `depth`.
    leaved used_vars as None for expected behavior.

    This won't generate absolutely everything, and I haven't tried to make this use some sensible
    distribution over expressions (whatever that would be).  If typ is None, it will draw from the
    random_types module level variable, which is currently just [type_t].

    An alternative approach would be to generate a random AST first, and fill it in.
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
        #print(random_used_vars)
        return term
    else:
        # possibilities:
        #  1. any typ: function-argument combination resulting in typ
        #  2. if typ is type_t: operator expression of typ (exclude non type_t options for now)
        #  3. if typ is type_t: binding expression of type_t
        #  4. if typ is functional: LFun of typ
        # ignore sets for now (variables with set types can be generated as part of option 1)
        # ignore iota for now
        options = [1]
        if typ == type_t:
            options.append(2)
            options.append(3)
        if typ.functional():
            options.append(4)
        choice = random.choice(options)
        def ctrl(**args):
            global random_used_vars
            return random_expr(depth=depth-1, used_vars=random_used_vars, **args)
        if choice == 1:
            return random_fa_combo(typ, ctrl)
        elif choice == 2:
            return random_tf_op_expr(ctrl)
        elif choice == 3:
            return random_binding_expr(ctrl)
        elif choice == 4:
            return random_lfun(typ, ctrl)
        else:
            raise NotImplementedError


import unittest

def test_repr_parse_abstract(self, depth):
    for i in range(1000):
        x = random_expr(depth=depth)
        result = repr_parse(x)
        if not result:
            print("Failure on depth %i expression '%s'" % (depth, repr(x)))
        self.assertTrue(result)

class MetaTest(unittest.TestCase):
    def setUp(self):
        self.ident = LFun(type_e, "x", "x")
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

    def test_parse(self):
        # overall: compare parsed TypedExprs with constructed TypedExprs
        # basic operator syntax
        self.assertEqual(TypedExpr.factory("(P_<e,t>(x_e) & P_<e,t>(x_e)) | P_<e,t>(x_e)"), self.body)
        # parenthesis reduction
        self.assertEqual(TypedExpr.factory("((P_<e,t>(x_e) & P_<e,t>(x_e)) | (P_<e,t>(x_e)))"), self.body)
        # parenthesis grouping
        self.assertNotEqual(TypedExpr.factory("P_<e,t>(x_e) & (P_<e,t>(x_e) | P_<e,t>(x_e))"), self.body)
        # variable binding syntax
        self.assertEqual(TypedExpr.factory("L x_e : x_e"), self.ident)
        self.assertRaises(parsing.ParseError, TypedExpr.factory, "L x_e : x_t")

    def test_reduce(self):
        self.assertEqual(self.ident(self.y).reduce(), self.y)

        # test: when a free variable in a function scopes under an operator, do not bind the variable on application        
        pmw_test1 = LFun(type_t, LFun(type_e, self.t & self.p, "x"), "p")
        pmw_test1b = LFun(type_e, self.t & self.t2, "x")
        self.assertNotEqual(pmw_test1.apply(self.t2), pmw_test1b)

        # Different version of the same test: direct variable substitution
        test2 = TypedExpr.factory("L y_e : L x_e : y_e")
        test2b = TypedExpr.factory("L x_e : x_e")
        self.assertNotEqual(test2.apply(self.x), test2b)

    # each of these generates 1000 random expressions with the specified depth, and checks whether their repr 
    # parses as equal to the original expression
    def test_repr_parse_0(self): test_repr_parse_abstract(self, 0)
    def test_repr_parse_1(self): test_repr_parse_abstract(self, 1)
    def test_repr_parse_2(self): test_repr_parse_abstract(self, 2)
    def test_repr_parse_3(self): test_repr_parse_abstract(self, 3)
    def test_repr_parse_4(self): test_repr_parse_abstract(self, 4)
    def test_repr_parse_5(self): test_repr_parse_abstract(self, 5)
    def test_repr_parse_6(self): test_repr_parse_abstract(self, 6)


# def setup():
#     hk = HK()
#     prop = FunType(hk.e,hk.t)
#     print(prop)
#     print(hk.hastype(prop))
#     testf = LFun(prop, hk.t, "x is a cat")
#     print(testf)



