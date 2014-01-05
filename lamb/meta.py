#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re
from numbers import Number
from lamb import types, utils, parsing
from lamb.types import TypeMismatch, type_e, type_t, type_n, type_property, type_transitive, OntoType, FunType
from lamb.utils import *
#import logic, utils

global _constants_use_custom, _type_system
_constants_use_custom = False

def constants_use_custom(v):
    global _constants_use_custom
    _constants_use_custom = v

# TODO: could consider associating TypedExpr with a type system rather than using the global variable.
# advantages: generality.  Disadvantages: may be a little pointless in practice?
def set_type_system(ts):
    global _type_system
    _type_system = ts

def get_type_system():
    return _type_system

def ts_unify(a, b):
    ts = get_type_system()
    return ts.unify(a, b)

def ts_compatible(a, b):
    ts = get_type_system()
    r = ts.unify(a,b)
    if r[0] is None:
        return False
    else:
        return True

def tp(s):
    ts = get_type_system()
    result = ts.type_parser(s)
    return result

#_type_system = types.UnderTypeSystem()
_type_system = types.under_system

unary_tf_ops = set(['~'])
binary_tf_ops = set(['>>', '<<', '&', '|', '<=>', '^'])
tf_ops = unary_tf_ops | binary_tf_ops

unary_num_ops = set(['-'])
binary_num_ops = set(['<', '<=', '>=', '>', '+', '-', '/', '*', '**'])
num_ops = unary_num_ops | binary_num_ops

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

    based on logic.Expr (from aima python).
    """
    def __init__(self, op, *args, defer=False):
        """
        Constructor for TypedExpr class.  This should generally not be called directly, rather, the factory function should be used.

        Takes an operator (op) and a number of arguments (*args).
          op: must be either a TypedExpr, or a string that represents one of the hard-coded binary/numeric operators.
          *args: whatever arguments are appropriate for the operator.
          defer: if True, will defer type inference.  Will still check types, though.  Intended for internal use.

        For any arguments that are strings, the factory method will be called. 
        Any arguments that are TypedExprs will be used as-is (no copies).  

        This function currently won't complain if you just hand it "x".  But _don't do this_, as terms should be constructed either 
        using the factory, or the constructor for TypedTerm.

        Raises:
          TypeMismatch if the operator and argument(s) do not have compatible types.
        """
        # TODO: unify convenience type guessing and type inference more generally?
        self.type_guessed = False
        type_sys = get_type_system()
        self.derivation = None

        if (op in basic_ops):
            #TODO: how to deal properly with the arguments here?
            # remove to factory, with specialized subclass
            raise NotImplementedError("Warning: constructing expression from deprecated basic operator '%s'" % op)
            self.args = [self.ensure_typed_expr(x) for x in args]
            uncertain = False
            for a in self.args:
                a.type_not_guessed()
                if a.type.undetermined:
                    uncertain = True
            # python 2.x was map(typed_expr, args)
            if op in tf_ops:
                self.type = type_t
            elif op in num_ops:
                self.type = type_n
            if uncertain:
                self.type = types.UndeterminedType(self.type)
            self.op = op
        # elif isinstance(op, LFun):
        #     if len(args) > 1:
        #         pass #TODO error handling
        #     arg = self.ensure_typed_expr(args[0])
        #     arg.type_not_guessed()
        #     unify_f, unify_b, unify_r = type_sys.unify_fa(op.type, arg.type)
        #     #if arg.type != op.argtype and not arg.type.undetermined:
        #     if unify_f is None:
        #         raise TypeMismatch(op, arg, "Lambda term+arg expression") #TODO: do I always want to check types here?
        #     self.type = unify_r #op.returntype
        #     #TODO is unification here the right thing?
        #     # TODO: it does not seem that I want to apply the results of unification to the LFun?
        #     if op.type == unify_f:
        #         self.op = op
        #     else:
        #         self.op = op.try_adjust_type(unify_f, "Function argument combination")
        #     if unify_b != arg.type:
        #         arg = arg.try_adjust_type(unify_b, "Function argument combination")                
        #         # if isinstance(arg, TypedTerm):
        #         #     arg = arg.copy()
        #         #     arg.type = unify_b
        #         # else:
        #         #     print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (arg.type, unify_a))
        #     self.args = [arg]
        elif isinstance(op, TypedExpr):
            if (len(args) > 1):
                # TODO: n-ary predicates
                raise TypeMismatch(op, args, "Function argument combination (too many arguments)")
            elif (len(args) == 0):
                print("Warning: vacuous container TypedExpr")
                self.type = op.type
                self.op = op
                self.args = list()
            else:
                history = False
                arg = self.ensure_typed_expr(args[0])
                unify_f, unify_a, unify_r = type_sys.local_unify_fa(op.type, arg.type)
                if unify_f is None:
                    raise TypeMismatch(op, arg, "Function argument combination (unification failed)")
                self.type = unify_r
                if op.type == unify_f or defer:
                    self.op = op
                else:
                    self.op = op.try_adjust_type(unify_f, "Function argument combination")
                    history = True
                if unify_a == arg.type or defer:
                    self.args = [arg]
                else:
                    self.args = [arg.try_adjust_type(unify_a, "Function argument combination")]
                    history = True
                if history:
                    #print("hi %s %s" % (repr(self.op), repr(self.args[0])))
                    # bit of a hack: build a derivation with the deferred version as the origin
                    old = TypedExpr(op, arg, defer=True)
                    derived(self, old, desc="Type inference")
            if isinstance(op, LFun):
                arg.type_not_guessed()
            else:
                self.type_guessed = op.type_guessed
        elif (len(args) == 0):
            # TODO this should never be called directly any more??  But may want to be able to call from subclasses?
            #raise ValueError("TypedExpr called with no arguments.  Should use function or term.  (op: '%s')" % repr(op))
            self.op = num_or_str(op)
            if isinstance(self.op, Number):
                self.type = type_n
            else:
                self.type = type_e # TODO is this the right thing to do? these were potentially predicate names in aima
            self.args = list()
        else:
            raise NotImplementedError("Don't know how to initialize TypedExpr with '%s: %s'" % (repr(op), repr(args)))

    # TODO: not comfortable with replicating this logic separately.  Need a better way.
    def recalc_type(self):
        type_sys = get_type_system()
        if (self.op in basic_ops):
            uncertain = False
            for a in self.args:
                if a.type.undetermined:
                    uncertain = True
            if self.op in tf_ops:
                self.type = type_t
            elif self.op in num_ops:
                self.type = type_n
            if uncertain:
                self.type = types.UndeterminedType(self.type)
        elif isinstance(self.op, LFun):
            unify_f, unify_a, unify_r = type_sys.local_unify_fa(self.op.type, self.args[0].type)
            #if arg.type != op.argtype and not arg.type.undetermined:
            self.type = unify_r
        elif isinstance(self.op, TypedExpr):
            if (len(args) == 0):
                self.type = self.op.type
            else:
                unify_f, unify_a, unify_r = type_sys.local_unify_fa(self.op.type, self.args[0].type)
                self.type = unify_r
            self.type_guessed = op.type_guessed
        elif (len(args) == 0):
            if isinstance(self.op, Number):
                self.type = type_n
            else:
                self.type = type_e
        else:
            raise NotImplementedError("Unhandled case in type recalculation")

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        #unify_a, unify_base = ts.local_unify(new_type, self.type)
        unify_a, unify_target = ts.local_unify(self.type, new_type)
        #print("new_type %s self type %s unify_a %s unify_target %s" % (new_type, self.type, unify_a, unify_target))
        if unify_a is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_a:
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
                new_op_type = types.UndeterminedType(types.FunType(self.args[0].type, unify_a))
                new_op = self.op.try_adjust_type(new_op_type, derivation_reason)
                if new_op is None:
                    return None
                self_copy = self.copy()
                self_copy.op = new_op
                # can't guarantee that we will have adopted the unified type, may still be weaker
                self_copy.type = new_op.type.right
                return derived(self_copy, self, derivation_reason)
            else:
                # should be term?
                if self.term():
                    new_op = self.copy()
                    new_op.type = unify_a
                    return derived(new_op, self, derivation_reason)
                else:
                    print("Warning: in type adjustment, unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
                    return self

    def __getitem__(self, key):
        a = [self.op] + self.args
        return a[key]

    def subst(self, i, s):
        """ Tries to consistently (relative to types) substitute s for element i of the TypedExpr.
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
        unify_a, unify_b = ts.unify(old.type, s.type)
        #print("%s, %s" % (unify_a, unify_b))
        if unify_a is None:
            raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
        if unify_b != s.type:
            s_a = s.try_adjust_type(unify_b)
            if s_a is None:
                raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
            #print("adjusting %s to %s" % (s,s_a))
            s = s_a
        if i == 0:
            c.op = s
            if c.op.type.functional() and c.args[0].type != unify_b.left:
                new_arg = c.args[0].try_adjust_type(unify_b.left)
                if new_arg is None:
                    raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
                c.args[0] = new_arg
            c.type = unify_b.right
        else:
            c.args[i-1] = s
            # leave type for c unchanged?
            if isinstance(c.op, TypedExpr):
                if c.op.type.left != unify_a:
                    new_op = c.op.try_adjust_type(FunType(unify_a, c.op.type.right))
                    if new_op is None: 
                        raise TypeMismatch(s, old, "Substitution for element %s of '%s'" % (i, repr(self)))
                    c.op = new_op
            else:
                pass
                # use a strict substitution rule for the time being
                #if unify_a != old.type:
                #    raise TypeMismatch(old, s, "Unify suggested strengthened type %s, but cannot accommodate" % unify_a)
                # or, silently succeed here?
                #raise NotImplementedError("Non-TypedExpr '%s' in subst" % c.op)
        return c

    @classmethod
    def parse_expr_string(cls, s, assignment=None):
        """Attempt to parse a string into a TypedExpr
        assignment: a variable assignment to use when parsing.

        First, try to see if the string is a lambda expression.  (See try_parse_lambda)
        Otherwise, do some regular expression magic, and then call eval.

        The gist of the magic:
          * replace some special cases with less reasonable operator names.  (This comes from AIMA logic)
          * find things that look like term names, and surround them with calls to the term factory function.
        """
        # test = cls.try_parse_lambda(s, assignment=assignment)
        # # see if we can succesfully get a lambda expression out of s
        # if test != None:
        #     vname, vtype, body = test
        #     if body is None:
        #         raise ValueError("Can't create body-less lambda expression from '%s'" % s)
        #     return LFun(vtype, body, vname)
        test = cls.try_parse_op_expr(s, assignment=assignment)
        if test != None:
            return test
        ## Replace the alternative spellings of operators with canonical spellings
        s = s.replace('==>', '>>').replace('<==', '<<')
        s = s.replace('<=>', '%').replace('=/=', '^')
        ## Replace a symbol or number, such as 'P' with 'Expr("P")'
        # TODO: handle numbers in strings, right now they end up as terms
        # TODO: handle greek letters
        # TODO: test this more
        # somewhat counterintuitively, this will match some incorrect strings, because error checking is done at the factory level
        #s = re.sub(r'([a-zA-Z0-9_]*[a-zA-Z0-9]+(_[a-zA-Z0-9\?\<\>,]*)?)', r'TypedExpr.term_factory("\1", assignment=assignment)', s)
        s = cls.expand_terms(s, assignment=assignment)
        ## Now eval the string.  (A security hole; do not use with an adversary.)
        # TODO: this won't necessarily do the right thing with assignment, can still result in inconsistent types
        #print(s)
        result = eval(s, {'TypedExpr':TypedExpr,'TypedTerm':TypedTerm, 'assignment': assignment, 'type_e': type_e})
        if isinstance(result, tuple):
            return Tuple(result)
        elif isinstance(result, set):
            return ListedSet(result)
        elif isinstance(result, dict) and len(result) == 0:
            return ListedSet(set())
        elif isinstance(result, TypedExpr):
            return result
        else:
            print("Warning: parse_expr_string returning non-TypedExpr")
            return result

    @classmethod
    def try_parse_lambda(cls, s, assignment=None):
        """Attempt to parse s as a lambda expression.  Used by the factory function.
        assignment: a variable assignment to use when parsing.

        Format: 'L v : b'
          * 'L' is one of 'lambda', 'L', or 'λ'
          * 'v' is a variable name expression (see try_parse_typed_term), e.g. x_e
          * 'b' is a function body, i.e. something parseable into a TypedExpr.

        If 'v' does not provide a type, it will attempt to guess one based on the variable name.
        The body will be parsed using an initial call to factory, with a shifted assignment using the new variable 'v'.

        Returns a tuple containing the variable, the type, and the body.  If you want a LFun, call the factory, not this.
        """
        # TODO: some kind of error messages / exceptions?
        next = None
        if s.startswith("lambda "):
            next = s[7:]
        elif s.startswith("L "):
            next = s[2:]
        elif s.startswith("λ"):
            next = s[1:]
        else:
            return None # failed to find proper initial chars
        l = next.split(":", 1)
        l = [x.strip() for x in l]
        #print("parsing with %s" % repr(l))
        if len(l) != 2:
            # TODO should the prefixes be treated as reserved?  Stronger error here?
            # right now, failure at this point leads to cryptic syntax errors on eval
            return None # failed to find properly terminated variable name
        (v, t) = cls.try_parse_typed_term(l[0])
        if not is_var_symbol(v):
            return None # failed to find variable name
        if t is None:
            # TODO: flag as a guessed type somehow?
            t = default_variable_type(v)
        body = None
        if len(l[1]) != 0:
            try:
                if assignment is None: 
                    assignment = dict()
                else:
                    # create a new one to avoid side effects
                    assignment = dict(assignment)
                assignment[v] = TypedTerm(v, t)
                #print("calling factory on '%s' with assignment %s" % (l[1], repr(assignment)))
                body = cls.factory(l[1], assignment=assignment)
            except Exception as e:
                print(e)
                raise ValueError("Lambda string has unparsable body ('%s')" % (s))
        return (v, t, body)

    @classmethod
    def try_parse_op_expr(cls, s, assignment=None):
        """Attempt to parse s as a unary operator expression.  Used by the factory function.
        assignment: a variable assignment to use when parsing.

        Format: 'Op v : b'
          * 'L' is one of 'lambda', 'L', 'λ', 'Forall', 'Exists', 
          * 'v' is a variable name expression (see try_parse_typed_term), e.g. x_e
          * 'b' is a function body, i.e. something parseable into a TypedExpr.

        If 'v' does not provide a type, it will attempt to guess one based on the variable name.
        The body will be parsed using an initial call to factory, with a shifted assignment using the new variable 'v'.

        Returns a subclass of UnaryOpExpr.
        """
        # TODO: some kind of error messages / exceptions?

        # normalize various ways of writing certain operators (bit of a hack)
        ops = {"lambda " : "L", "L " : "L", "λ" : "L", "Iota ": "I", "Forall " : "A", "Exists " : "E", "Set " : "S"}
        # map operators to classes (for standardized BindingOp constructors)
        op_classes = {"L" : LFun, "I" : IotaUnary, "A" : ForallUnary, "E": ExistsUnary, "S" : ConditionSet}
        # To add a new unary variable-binding operator to the parser, decide on a normalized operator string and add
        # it to ops, and then add the right mapping to op_classes.  If your operator has a non-standard constructor,
        # instead of adding it to op_classes, add a new condition to the if section at the end of this function.
        next = None
        op = None
        for k in ops.keys():
            if s.startswith(k):
                op = ops[k]
                next = s[len(k):]
                break
        if op is None:
            return None # failed to find proper initial chars
        l = next.split(":", 1)
        l = [x.strip() for x in l]
        #print("parsing with %s" % repr(l))
        if len(l) != 2:
            # TODO should the prefixes be treated as reserved?  Stronger error here?
            # right now, failure at this point leads to cryptic syntax errors on eval
            return None # failed to find properly terminated variable name
        (v, t) = cls.try_parse_typed_term(l[0])
        if not is_var_symbol(v):
            return None # failed to find variable name
        if t is None:
            # TODO: flag as a guessed type somehow?
            t = default_variable_type(v)
        body = None
        if len(l[1]) != 0:
            try:
                if assignment is None: 
                    assignment = dict()
                else:
                    # create a new one to avoid side effects
                    assignment = dict(assignment)
                assignment[v] = TypedTerm(v, t)
                #print("calling factory on '%s' with assignment %s" % (l[1], repr(assignment)))
                body = cls.factory(l[1], assignment=assignment)
            except Exception as e:
                print(e)
                raise ValueError("Operator expression has unparsable body ('%s')" % (s))

        if body is None:
            raise ValueError("Can't create body-less operator expression from '%s'" % s)
        if op in op_classes:
            return op_classes[op](var=v, vtype=t, body=body)
        else:
            raise ValueError("Unknown op " + op)
        # if op == "L":
        #     return LFun(var=v, vtype=t, body=body)
        # elif op == "E":
        #     return ExistsUnary(var=v, vtype=t, body=body)
        # elif op == "A":
        #     return ForallUnary(var=v, vtype=t, body=body)
        # elif op == "I":
        #     return IotaUnary(var=v, vtype=t, body=body)
        # elif op == "S":
        #     return ConditionSet(var=v, vtype=t, body=body)
        # 


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
    def try_parse_typed_term(cls, s, assignment=None):
        v, typ, end = cls.parse_term(s, i=0, return_obj=False, assignment=assignment)
        return (v, typ)

    @classmethod
    def try_parse_typed_term_old(cls, s, assignment=None):
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
        # TODO: should this just return a typed term??
        l = s.strip().split("_", 1)
        v = l[0]
        t = None
        if l[0].isnumeric():
            # note that this will override any provided type -- maybe a bad idea?
            return (int(l[0]), type_n)
        if not is_symbol(v):
            raise ValueError("Can't parse term: '%s' is not a symbol." % s)
        if len(l) == 1 or len(l[1]) == 0:
            if (assignment is not None) and v in assignment:
                # inherit type from context
                return (v, assignment[v].type)
            else:
                # no type provided by context or string
                return (v, None)
        t = cls.try_parse_type(l[1])
        # disallow overloading of variables with different types
        # TODO: should this not be in the parsing function?
        if assignment is not None and v in assignment and assignment[v].type != t:
            raise TypeMismatch(s, assignment[v], "Variable type inheritence")
        return (v,t)

    @classmethod
    def find_term_locations(cls, s, i=0):
        term_re = re.compile(r'([a-zA-Z0-9]+)(_)?')
        unfiltered_result = parsing.find_pattern_locations(term_re, s, i=i, end=None)
        result = list()
        for r in unfiltered_result:
            if r.start() > 0 and s[r.start() - 1] == ".":
                # result is prefaced by a ".", and so therefore is a functional call or attribute
                continue
            result.append(r)
        return result


    @classmethod
    def expand_terms(cls, s, i=0, assignment=None):
        """Treat terms as macros for term_factory calls.  Attempt to find all term strings, and replace them with eval-able factory calls.

        This is an expanded version of the original regex approach; one reason to move away from that is that this will truely parse the types."""
        terms = cls.find_term_locations(s, i)
        offset = 0
        for t in terms:
            if t.start() + offset < i:
                # parsing has already consumed this candidate term, ignore.  (E.g. an "e" in a type signature.)
                continue
            #print("parsing '%s' at: '%s'" % (t.group(0), s[t.start()+offset:]))
            (name, typ, end) = cls.parse_term(s, t.start() + offset, return_obj=False, assignment=assignment)
            if name is None:
                print("Warning: unparsed term '%s'" % t.group(0)) # TODO: more?
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
                    u_l, u_r = ts.unify(typ, assignment[term_name.group(1)].type)
                    if u_l is None:
                        raise TypeMismatch(cls.term_factory(term_name.group(1), typ), assignment[term_name.group(1)], "Type inheritence from assignment")
                    else:
                        # TODO: better logic?
                        typ = u_l

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
                result = result.try_adjust_type(typ)
            return result
        elif (isinstance(s, str)):
            if typ is None and not preparsed:
                v, typ = cls.try_parse_typed_term(s, assignment=assignment)
            else:
                v = s
            if _constants_use_custom and not is_var_symbol(v):
                return CustomTerm(v, typ=typ)
            else:
                return TypedTerm(v, typ=typ)
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
        #print("    factory: args %s" % repr(args))
        #if assignment is None:
        #    assignment = {}
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
                return cls.parse_expr_string(s, assignment)
            else:
                raise NotImplementedError
        else:
            # argument length > 1

            # this is redundant with the constructor, but I can't currently find a way to simplify
            args = (args[0],) + tuple([cls.ensure_typed_expr(a) for a in args[1:]])


            if isinstance(args[0], str):
                # special case to test for lambda terms
                # see if we can succesfully get a lambda expression out of args[0]
                test = cls.try_parse_lambda(args[0], assignment)
                if test != None:
                    vname, vtype, body = test
                    if body != None or len(args) > 2:
                        raise ValueError("Too many bodies for lambda expression from '%s'" % repr(args))
                    return LFun(vtype, args[1], vname)
                else:
                    if args[0] in op_symbols:
                        return op_expr_factory(*args)
                    else:
                        raise ValueError("Don't know how to build TypedExpr from multi-element list '%s'" % repr(args))
            # package longer arg lengths in Tuples.
            if len(args) > 2:
                packaged_args = Tuple(args[1:])
                args = (args[0], packaged_args)
            if isinstance(args[0], TypedExpr) and (not args[0].type.functional()) and args[0].type_guessed:
                # TODO more general case: coerce any guessed type, not just basic types?
                # special case: see if the type of the operator is guessed and coerce accordingly
                if len(args) == 2 and isinstance(args[1], TypedExpr):
                    #TODO make this smarter.  What if arg is a string?
                    # TODO: should type t be the default return type?
                    # prevent future coercion of the argument
                    args[1].type_not_guessed()
                    coerced_op = args[0].try_coerce_new_argument(args[1].type)
                    #coerced_op = TypedTerm(args[0].op, FunType(args[1].type, type_t))
                    if coerced_op is not None:
                        print("warning: coerced guessed type %s for '%s' into %s, to match argument '%s'" % (args[0].type, repr(args[0]), coerced_op.type, repr(args[1])))
                        args = (coerced_op,) + args[1:]
                    else:
                        print("warning: unable to coerce guessed type %s for '%s' to match argument '%s' (type %s)" % (args[0].type, repr(args[0]), repr(args[1]), args[1].type))
                # no action in else case??
            if isinstance(args[0], TypedExpr) and args[0].type.functional() and not args[0].type.left.undetermined and args[1].type.undetermined:
                # special case: applying undetermined type to function, would have to coerce to do full application
                # TODO: implement coercion here?
                pass
            # if we get to this point, args[0] should be the operator, and the rest of the list arguments to the operator.
            return TypedExpr(*args)

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
            r_adjusted = result.try_adjust_type(typ)
            if r_adjusted is None:
                raise TypeMismatch(result, typ, mode="type adjustment")
            else:
                return r_adjusted

    def try_coerce_new_argument(self, typ, remove_guessed=False):
        if not self.type_guessed:
            return None
        if not isinstance(self.op, TypedExpr):
            return None
        result = self.op.try_coerce_new_argument(typ)
        if result:
            copy = TypedExpr(result, *self.args)
            if (remove_guessed):
                result.type_guessed = False
            return copy
        else:
            return None

    def type_not_guessed(self):
        self.type_guessed = False
        if isinstance(self.op, TypedExpr):
            self.op.type_not_guessed()

    def copy(self):
        """Make a copy of the expression.  Will not produce a deep copy.

        Must be overridden by subclasses, or this will go wrong.
        """
        # TODO should this call the factory?
        c = TypedExpr(self.op, *self.args)
        #c.derivation = self.derivation #TODO: should I do this?
        assert c == self
        return c

    def under_assignment(self, assignment):
        # do this first so that any errors show up before the recursive step
        if assignment is None:
            a2 = dict()
        else:
            a2 = {key: self.ensure_typed_expr(assignment[key]) for key in assignment}
        return variable_replace_strict(self, a2)

    # the next two functions are clearly inefficient, and could be replaced by memoization (e.g. 'director strings' or 
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

    def term(self):
        return (isinstance(self.op, str) and len(self.args) == 0)

    def atomic(self):
        if isinstance(self.op, TypedExpr):
            return False
        for a in self.args:
            if isinstance(a, TypedExpr):
                return False
        return True

    def reduce(self):
        """if there are arguments to op, see if a single reduction is possible."""
        if len(self.args) == 0:
            return self
        elif isinstance(self.op, LFun):
            return derived(self.op.apply(self.args[0]), self, desc="F-A reduction")
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
        # this is a dumb strategy, probably not fully general
        result = self
        dirty = False
        if isinstance(result.op, TypedExpr):
            new_op = result.op.reduce_all()
            if new_op is not result.op:
                dirty = True
                next_step = result.copy()
                next_step.op = new_op
                result = derived(next_step, result, desc="Recursive reduction of op")
        new_result = result.reduce()
        if new_result is not result:
            dirty = True
            result = new_result # no need to add a derivation here, reduce will do that already
        # do this twice in case reduce did something
        if isinstance(result.op, TypedExpr):
            new_op = result.op.reduce_all()
            if new_op is not result.op:
                if not dirty:
                    dirty = True
                next_step = result.copy()
                next_step.op = new_op
                result = derived(next_step, result, desc="Recursive reduction of op")
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
                result = derived(next_step, result, desc=reason)
        return result # could instead just do all the derivedness in one jump here


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

    def __call__(self, *args):
        """Attempt to construct a saturated version of self."""
        # TODO possibly move this to TypedTerm...
        # note: all error checking occurs in the factory.
        
        #if not is_symbol(self.op):
        #    raise ValueError("Don't know how to saturate '%s'" % repr(self))
        #if self.args:
        #    raise ValueError("'%s' appears to be already saturated (attempted extra args: '%s')." % (repr(self), repr(args)))
        return TypedExpr.factory(self, *args)


    def __repr__(self):
        "Show something like 'P' or 'P(x, y)', or '~P' or '(P | Q | R)'"
        if not self.args:         # Constant or proposition with arity 0
            return repr(self.op)
        elif isinstance(self.op, LFun):
            return "[%s](%s)" % (repr(self.op), ', '.join([repr(a) for a in self.args]))
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
        if not self.args:
            return ensuremath(str(self.op))
        elif isinstance(self.op, LFun):
            return ensuremath("[%s](%s)" % (self.op.latex_str(), ', '.join([a.latex_str() for a in self.args])))
        elif isinstance(self.op, TypedExpr) and (self.op.type.functional() or self.op.type.undetermined):  # Functional or propositional operator
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
        """x and y are equal iff their ops and args are equal."""
        # need to explicitly check this in case recursion accidentally descends into a string Op
        # TODO revisit
        if isinstance(other, TypedExpr):
            return (other is self) or (self.op == other.op and self.args == other.args)
        else:
            return False
        #TODO: equality by semantics, not syntax?

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        "Need a hash method so Exprs can live in dicts."
        return hash(self.op) ^ hash(tuple(self.args))

    def __getitem__(self, i):
        return ([self.op] + self.args).__getitem__(i)

    def __len__(self):
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


class Tuple(TypedExpr):
    def __init__(self, args, typ=None):
        self.op = "Tuple"
        self.derivation = None
        self.args = list()
        type_accum = list()
        for i in range(len(args)):
            if typ is None:
                a_i = self.ensure_typed_expr(args[i])
            else:
                a_i = self.ensure_typed_expr(args[i], typ=typ[i])
            self.args.append(a_i)
            type_accum.append(a_i.type)
        self.type = types.TupleType(*type_accum)

    def copy(self):
        return Tuple(self.args)

    def term(self):
        return False

    def tuple(self):
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
    def __init__(self, varname, typ=None, latex_op_str=None):
        self.op = varname
        self.derivation = None
        if typ is None:
            self.type = default_type(varname)
            self.type_guessed = True
        else:
            self.type_guessed = False
            self.type = typ
        self.args = list()
        self.suppress_type = False
        self.latex_op_str = latex_op_str

    def copy(self):
        return TypedTerm(self.op, typ=self.type)

    def __call__(self, *args):
        # TODO: type checking here?  Answer: no, because arg may not yet be a TypedExpr
        return TypedExpr.factory(self, *args)

    def free_variables(self):
        if is_var_symbol(self.op):
            return {self.op}
        else:
            return set()

    def term(self):
        return True

    def constant(self):
        return not is_var_symbol(self.op)

    def variable(self):
        return is_var_symbol(self.op)

    def __repr__(self):
        return self.op

    def show_type(self):
        if self.suppress_type:
            return False
        if suppress_constant_type and self.constant():
            return False
        if suppress_constant_predicate_type:
            if self.constant() and self.type.functional():
                if (self.type.left == types.type_e or isinstance(self.type.left, types.TupleType)) and self.type.right == types.type_t:
                    return False
        return True

    def try_coerce_new_argument(self, typ, remove_guessed = False):
        if not self.type_guessed:
            return None
        #self.type = self.type.add_internal_argument(typ)
        #coerced_op = TypedTerm(self.op, self.type.add_internal_argument(typ))
        coerced_op = self.copy()
        # TODO: not 100% sure this is right, and may lead to complications down the road
        coerced_op.type = self.type.add_internal_argument(typ)
        if not remove_guessed:
            coerced_op.type_guessed = True
        return coerced_op

    def latex_str(self):
        if self.latex_op_str is None:
            op = self.op
        else:
            op = self.latex_op_str
        if not self.show_type():
            return ensuremath("{%s}" % op)
        else:
            return ensuremath("{%s}_{%s}" % (op, self.type.latex_str()))

    def _repr_latex_(self):
        return self.latex_str()

class CustomTerm(TypedTerm):
    def __init__(self, varname, custom_english=None, suppress_type=True, small_caps=True, typ=None):
        TypedTerm.__init__(self, varname, typ=typ)
        self.custom = custom_english
        self.sc = small_caps
        self.suppress_type = suppress_type
        self.verbal = False
        # TODO: check type against custom string

    def copy(self):
        return CustomTerm(self.op, custom_english=self.custom, suppress_type=self.suppress_type, small_caps=self.sc, typ=self.type)

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
        self.derivation = None
        self.op = op
        # default behavior: type of body is type of whole
        self.args = [self.ensure_typed_expr(arg1, typ)]
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


    def type_constraints(self):
        # TODO: generalize somehow
        ts = get_type_system()
        unify_a, unify_base = ts.local_unify(self.args[0].type, self.type)
        if unify_a is None:
            raise TypeMismatch(MiniOp.from_op(self), self.args[0], mode="Unary operator")
        if self.args[0].type != unify_a:
            if isinstance(self.args[0], TypedTerm):
                self.args[0] = self.args[0].copy()
                self.args[0].type = unify_a
            else:
                print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.args[0].type, unify_a))

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

    Because of the way the copy function works, it is currently not suited for direct instantiation."""
    def __init__(self, typ, op, arg1, arg2, op_name_uni=None, op_name_latex=None, tcheck_args=True):
        self.derivation = None
        self.op = op
        if tcheck_args:
            self.args = [self.ensure_typed_expr(arg1, typ), self.ensure_typed_expr(arg2, typ)]
        else:
            self.args = [self.ensure_typed_expr(arg1), self.ensure_typed_expr(arg2)]
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
        super().__init__(type_t, "^", arg1, arg2, "!=", "\\not=")

class BinaryGenericEqExpr(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        arg1 = self.ensure_typed_expr(arg1)
        # maybe raise the exception directly?
        arg2 = self.ensure_typed_expr(arg2, arg1.type)
        super().__init__(type_t, "==", arg1, arg2, "==", "=", tcheck_args = False)

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
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            super().__init__(type_n, op, arg1, arg2, op_uni, op_latex)
    return BinOp

def binary_num_rel(op, op_uni=None, op_latex=None):
    if op_uni is None:
        op_uni = op
    if op_latex is None:
        op_latex = op
    class BinOp(BinaryOpExpr):
        def __init__(self, arg1, arg2):
            # this is a bit redundant but it works
            super().__init__(type_t, op, self.ensure_typed_expr(arg1, types.type_n), self.ensure_typed_expr(arg2, types.type_n), op_uni, op_latex, tcheck_args=False)
    return BinOp

class SetContains(BinaryOpExpr):
    def __init__(self, arg1, arg2):
        # seems like the best way to do the mutual type checking here?  Something more elegant?
        arg1 = self.ensure_typed_expr(arg1)
        arg2 = self.ensure_typed_expr(arg2, types.SetType(arg1.type))
        arg1 = self.ensure_typed_expr(arg1, arg2.type.content_type)
        super().__init__(type_t, "in", arg1, arg2, "∈", "\\in{}", tcheck_args=False)

    def copy(self):
        return SetContains(self.args[0], self.args[1])


class UnaryNegativeExpr(UnaryOpExpr):
    def __init__(self, body):
        super().__init__(type_n, "-", body, "-", "-")


BinaryLExpr = binary_num_rel("<", "<", "<")
BinaryLeqExpr = binary_num_rel("<=", "<=", "\\leq{}")
BinaryGeqExpr = binary_num_rel(">=", ">=", "\\geq{}")
BinaryGExpr = binary_num_rel(">", ">", ">")
BinaryPlusExpr = binary_num_op("+", "+", "+")
BinaryMinusExpr = binary_num_op("-", "-", "-")
BinaryDivExpr = binary_num_op("/", "/", "/")
BinaryTimesExpr = binary_num_op("*", "*", "*")
BinaryExpExpr = binary_num_op("**", "**", "**")

unary_symbols_to_op_exprs = {"~" : UnaryNegExpr,
                        "-" : UnaryNegativeExpr}

# not implemented: << (left implication)
# note that neq is for type t only.
binary_symbols_to_op_exprs = {
                        "&" : BinaryAndExpr,
                        "|" : BinaryOrExpr,
                        ">>" : BinaryArrowExpr,
                        "<=>" : eq_factory,
                        "==" : eq_factory,
                        "%" : BinaryNeqExpr,
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
    """abstract class for a unary operator that binds a single variable in its body."""
    def __init__(self, vartype, typ, op, var, body, op_name_uni=None, op_name_latex=None, body_type = None):
        if body_type is None:
            body_type = typ
        # maybe add way to block body type checking in init altogether?
        self.op = op
        if op_name_uni is None:
            self.op_name = op
        else:
            self.op_name = op_name_uni
        if op_name_latex is None:
            self.op_name_latex = op_name_uni
        else:
            self.op_name_latex = op_name_latex
        if isinstance(var, TypedTerm):
            if var.type != vartype:
                pass #TODO be less forgiving?
            self.varname = var.op
        else:
            self.varname = str(var) # TODO fail on other types?
        if not is_var_symbol(self.varname):
            raise ValueError("Need variable name (got '%s')" % var)
        self.vartype = vartype
        self.type = typ
        self.derivation = None
        self.var_instance = TypedTerm(self.varname, self.vartype)
        #self.body = typed_expr(body)
        self.args = [self.ensure_typed_expr(body, body_type, assignment={self.varname: self.var_instance})]

    @property
    def body(self):
        return self.args[0]

    def copy(self):
        return BindingOp(vartype=self.vartype, typ=self.type, op=self.op, var=self.var_name, body=self.body, op_name_uni = self.op_name_uni, op_name_latex=self.op_name_latex)
        #raise NotImplementedError

    def alpha_convert(self, new_varname):
        """Produce an alphabetic variant of the expression w.r.t. the bound variable, with new_varname as the new name.

        Returns a copy.  Will not affect types of either the expression or the variables."""
        new_self = self.copy()
        new_self.args[0] = variable_convert(self.args[0], {self.varname: new_varname})
        new_self.varname = new_varname
        return new_self

    def latex_op_str(self):
        return "(%s \\:%s_{%s}) \\: . \\:" % (self.op_name_latex, 
                                                self.varname, 
                                                self.vartype.latex_str())

    def latex_op_str_short(self):
        return "%s %s_{%s} \\: . \\:" % (self.op_name_latex, 
                                                self.varname, 
                                                self.vartype.latex_str())

    def __str__(self):
        return "(%s %s). %s\nType: %s" % (self.op_name, self.varname, repr(self.body), self.type)

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
        return "(%s %s). %s" % (self.op_name, self.varname, repr(self.body))

    def free_variables(self):
        return super().free_variables() - {self.varname}

    def bound_variables(self):
        return super().bound_variables() | {self.varname}

    def vacuous(self):
        return self.varname in super().free_variables()

    def term(self):
        return False

 



class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""
    def __init__(self, vtype, body, var="x"):
        body = self.ensure_typed_expr(body)
        super().__init__(vartype=vtype, typ=types.SetType(vtype), op="(Set %s)" % var, var=var, body=body, op_name_uni="Set", op_name_latex="Set", body_type=types.type_t)
        #self.type = types.SetType(vtype)
        self.latex_op_str = self.latex_op_str_short

    def copy(self):
        return ConditionSet(self.vartype, self.body, self.varname)

    def structural_singleton(self):
        pass

    def term(self):
        return False

    def __repr__(self):
        return "{%s | " % self.varname + repr(self.body) + "}"

    def latex_str(self, parens=True):
        return ensuremath("\{%s_{%s}\:|\: " % (self.varname, self.vartype) + self.body.latex_str() + "\}")

    def __lshift__(self, i):
        return SetContains(i, self)

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname)

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unify_a, unify_b = ts.local_unify(new_type, self.type)
        if unify_a is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_b:
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            inner_type = unify_b.content_type
            char = self.to_characteristic()
            sub_var = TypedTerm(self.varname, inner_type)
            new_condition = char.apply(sub_var)
            return derived(ConditionSet(inner_type, new_condition, self.varname), self, derivation_reason)

class SingletonSet(TypedExpr):
    def __init__(self, body):
        self.args = [self.ensure_typed_expr(body)]
        self.op = "Set"
        self.type = types.SetType(body.type)
        self.derivation = None

    def copy(self):
        return SingletonSet(self.args[0])

    @property
    def body(self):
        return self.args[0]

    def term(self):
        return False

    def __repr__(self):
        return "{" + repr(self.args[0]) + "}"

    def latex_str(self, parens=True):
        return ensuremath("\{" + self.args[0].latex_str() + "\}")

    def to_condition_set(self):
        return ConditionSet(self.type, BinaryGenericEqExpr(self.ensure_typed_expr("x", self.args[0].type), self.args[0]))

    #def __contains__(self, i):
    #    return SetContains(i, self)

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unify_a, unify_b = ts.local_unify(new_type, self.type)
        if unify_a is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_b:
            return self
        else: # either input or output type can be strengthened
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            inner_type = unify_b.content_type
            content = self.args[0].try_adjust_type(inner_type, derivation_reason)
            return derived(SingletonSet(content), self, derivation_reason)

class ListedSet(TypedExpr):
    def __init__(self, iterable, typ=None):
        s = set(iterable) # just make it a set first, remove duplicates, flatten order
        self.args = [self.ensure_typed_expr(a) for a in s]
        if len(self.args) == 0 and typ is None:
            typ = types.undetermined_type
        elif typ is None:
            typ = self.args[0].type
        for i in range(len(self.args)): # type checking TODO: this isn't right, would need to pick the strongest type
            self.args[i] = self.ensure_typed_expr(self.args[i], typ)
        self.op = "Set"
        self.type = types.SetType(typ)
        self.derivation = None

    def copy(self):
        return ListedSet(self.args)

    def term(self):
        return False

    def __lshift__(self, i):
        return SetContains(i, self)

    def set(self):
        return set(self.args)

    def cardinality(self):
        return len(self.args)

    def to_condition_set(self):
        # ensure that we build a condition set from a variable that is not free in any of the members
        varname = self.find_safe_variable(starting="x")
        conditions = [BinaryGenericEqExpr(TypedTerm(varname, a.type), a) for a in self.args]
        return ConditionSet(self.type.content_type, BinaryOrExpr.join(*conditions), var=varname)


    def __repr__(self):
        return "{" + ", ".join([repr(a) for a in self.args]) + "}"

    def latex_str(self):
        inner = ", ".join([a.latex_str() for a in self.args])
        return ensuremath("\{" + inner + "\}")

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unify_a, unify_b = ts.local_unify(new_type, self.type)
        if unify_a is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_b:
            return self
        else:
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            inner_type = unify_b.content_type
            content = [a.try_adjust_type(inner_type, derivation_reason) for a in self.args]
            return derived(ListedSet(content), self, derivation_reason)

class ForallUnary(BindingOp):
    def __init__(self, vtype, body, var="x"):
        body = self.ensure_typed_expr(body)
        super().__init__(vtype, types.type_t, "∀%s. " % var, var, body, op_name_uni="∀", op_name_latex="\\forall{}")
        self.latex_op_str = self.latex_op_str_short

    def copy(self):
        return ForallUnary(self.vartype, self.body, self.varname)

    # def __str__(self):
    #     return "∀%s. %s\nType: t" % (self.varname, repr(self.body))

    # def latex_str_long(self):
    #     return "$\\forall %s_{%s} \\m. %s $\\\\ Type: $t$" % (self.varname, 
    #                                                                                 self.vartype.latex_str(),  
    #                                                                                 self.body.latex_str())
    # def latex_str(self):
    #     return ensuremath("\\forall %s_{%s} \\: . \\: %s" % (self.varname, 
    #                                             self.vartype.latex_str(),  
    #                                             self.body.latex_str()))
    # # TODO: if this is uncommented, it blocks inheritence of __hash__
    # # will need to remember to fix hashing as well once I implement the TODO below.  (What are the rules?)
    # #def __eq__(self, other):
    # #    # TODO: implement equality up to alphabetic variants.
    # #    # as is, alphabetic variants will not be equal.
    # #    return super().__eq__(other)

    # def __repr__(self):
    #     return "∀%s. %s" % (self.varname, repr(self.body))

class ExistsUnary(BindingOp):
    def __init__(self, vtype, body, var="x"):
        body = self.ensure_typed_expr(body)
        #if body.type != types.type_t:
        #    raise TypeMismatch
        super().__init__(vtype, types.type_t, "∃%s. " % var, var, body, op_name_uni="∃", op_name_latex="\\exists{}")
        self.latex_op_str = self.latex_op_str_short

    def copy(self):
        return ExistsUnary(self.vartype, self.body, self.varname)

class IotaUnary(BindingOp):
    def __init__(self, vtype, body, var="x"):
        body = self.ensure_typed_expr(body)
        #if body.type != types.type_t:
        #    raise TypeMismatch
        super().__init__(vartype=vtype, typ=vtype, op=("i%s. " % var), var=var, body=body, op_name_uni="i", op_name_latex="\\iota{}", body_type=types.type_t)
        self.latex_op_str = self.latex_op_str_short

    def copy(self):
        return IotaUnary(self.vartype, self.body, self.varname)


class LFun(BindingOp):
    """A typed function.  Can itself be used as an operator in a TypedExpr.

    """
    def __init__(self, vtype, body, var="x"):
        #print("LFun constructor: %s, '%s', %s" % (argtype, repr(body), var))
        body = self.ensure_typed_expr(body)
        super().__init__(vartype=vtype, typ=FunType(vtype, body.type), op="λ%s. " % var, var=var, body=body, op_name_uni="λ", op_name_latex="\\lambda{}", body_type=body.type)
        #self.argtype = argtype
        #self.returntype = body.type
        self.latex_op_str = self.latex_op_str_short

        #self.op = "λ%s. " % var

    @property
    def argtype(self):
        return self.type.left

    @property
    def returntype(self):
        return self.type.right

    def copy(self):
        return LFun(self.argtype, self.body, self.varname)

    # def __str__(self):
    #     return "λ%s. %s\nType: <%s,%s>" % (self.varname, repr(self.body), self.argtype, self.returntype)

    # def latex_str_long(self):
    #     return "$\\lambda %s_{%s} \\m. %s $\\\\ Type: $\\stype{\\stype{%s,%s}}$" % (self.varname, 
    #                                                                                 self.argtype.latex_str(),  
    #                                                                                 self.body.latex_str(),
    #                                                                                 self.argtype.latex_str(),
    #                                                                                 self.returntype.latex_str())
    # def latex_str(self):
    #     return ensuremath("\\lambda %s_{%s} \\: . \\: %s" % (self.varname, 
    #                                             self.argtype.latex_str(),  
    #                                             self.body.latex_str()))
    # # TODO: if this is uncommented, it blocks inheritence of __hash__
    # # will need to remember to fix hashing as well once I implement the TODO below.  (What are the rules?)
    # #def __eq__(self, other):
    # #    # TODO: implement equality up to alphabetic variants.
    # #    # as is, alphabetic variants will not be equal.
    # #    return super().__eq__(other)

    # def _repr_latex_(self):
    #     return self.latex_str()

    # def __repr__(self):
    #     return "λ%s. %s" % (self.varname, repr(self.body))

    def try_adjust_type(self, new_type, derivation_reason=None):
        """Attempts to adjust the type of self to be compatible with new_type.  
        If the types already match, it return self.
        If it succeeds, it returns a modified _copy_ of self.  
        If unify suggests a strengthened type, but it can't get there, it returns self and prints a warning.
        If it fails completely, it returns None."""
        ts = get_type_system()
        unify_a, unify_b = ts.local_unify(new_type, self.type)
        if unify_a is None:
            #print("Warning: unify suggested a strengthened arg type, but could not accommodate: %s -> %s" % (self.type, unify_a))
            return None
        if self.type == unify_b:
            return self
        else: # either input or output type can be strengthened
            #new_body = self.body.try_adjust_type(unify_a.right) # will only make copy if necessary
            if derivation_reason is None:
                derivation_reason = "Type adjustment"
            new_argtype = unify_b.left
            if self.argtype != unify_b.left:
                # arg type needs to be adjusted, and hence all instances of the bound variable as well.  Do this with beta reduction.
                new_var = TypedTerm(self.varname, unify_b.left)
                new_body = self.apply(new_var)
            else:
                new_body = self.body
            #if new_body.type != unify_a.right:
            new_body = new_body.try_adjust_type(unify_b.right, derivation_reason) # will only make copy if necessary
            new_fun = LFun(new_argtype, new_body, self.varname)
            return derived(new_fun, self, derivation_reason)
        

    def apply(self,arg):
        # do I really want flexible equality here??
        # TODO: return to this.  Right now a type mismatch still gets raised during beta reduction.
        ts = get_type_system()
        if ts.eq_check(self.argtype, arg.type):
            # first check for potential variable name collisions when substituting, and the substitute
            #TODO: do I want to actually return the result of alpha converting?  May be needed later?
            new_self = alpha_convert_new(self, unsafe_variables(self, arg))
            # TODO: the copy here is a hack.  Right now identity functions result in no copying at all, leading to very
            # wrong results.  This needs to be tracked down to its root and fixed.
            return (beta_reduce_ts(new_self.body, new_self.varname, arg)).copy()
            #return beta_reduce_ts(self.body, self.varname, alpha_convert(arg, unsafe_variables(self, arg)))
        else:
            raise TypeMismatch(self,arg, "Application")

    def __call__(self, *args):
        """Create a new expression that is the result of applying arg to the function

        call + reduce is equivalent to apply, for an LFun"""
        return TypedExpr.factory(self, *args)

def unsafe_variables(fun, arg):
    return arg.free_variables() & fun.body.bound_variables()

def beta_reduce(t, varname, s):
    """Do beta reduction on t, substituting in s.  Will not affect t itself.

    t: a TypedExpr of some kind.
    varname: the name of the variable we are substituting for in t.
    s: an expression to replace the variable with.  (Can be a parseable string or a TypedExpr.)

    If t is a variable, will return the substitute itself.  Otherwise, will recurse into t.  While the 
    return value may share sub-structure with `t`, this function will return copies above any point that is changed.
    """
    if not is_var_symbol(varname):
        raise ValueError("Beta reduction passed non-variable '%s'" % varname)
    subst = TypedExpr.ensure_typed_expr(s)            
    if varname in t.free_variables():
        #print("asdf %s, %s" % (varname, repr(t)))
        if (t.term() and t.op == varname):
            if t.type != subst.type:
                raise TypeMismatch(t, subst, "Beta reduction") # TODO make less cryptic
            #print("substituting with %s" % subst)
            return subst # TODO copy??
        # we will be changing something in this expression, but not at this level of recursion, so make a copy.
        t = t.copy()
        if isinstance(t.op, TypedExpr):
            # operator is a possibly complex TypedExpr
            t.op = beta_reduce(t.op, varname, subst)
        # TODO: check string ops?
        # TODO: check assumption: all variables are TypedExprs.

        for i in range(len(t.args)):
            if isinstance(t.args[i], TypedExpr):
                t.args[i] = beta_reduce(t.args[i], varname, subst)
                #print("beta reduce returning %s" % t.args[i])
            else:
                # ???
                raise ValueError("problem during beta reduction...") # TODO: make less cryptic
        #print("beta reduce returning %s" % t.args)
    return t

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
        t = t.copy()
        if isinstance(t.op, TypedExpr):
            # operator is a possibly complex TypedExpr
            new_op = beta_reduce_ts(t.op, varname, subst)
            t = t.subst(0, new_op)
        # TODO: check string ops?
        # TODO: check assumption: all variables are TypedExprs.

        for i in range(len(t.args)):
            if not isinstance(t.args[i], TypedExpr):
                # ???
                raise ValueError("problem during beta reduction...") # TODO: make less cryptic
            new_arg_i = beta_reduce_ts(t.args[i], varname, subst)
            t = t.subst(i+1, new_arg_i)
        #print("beta reduce returning %s" % t.args)
    return t


def old_variable_convert(expr, m):
    """Rename free instances of variables in expr, as determined by the map m.

    Operates on a copy.
    expr: a TypedExpr
    m: a map from strings to strings."""
    # TODO: replace this with a call to variable_replace?  Don't think this would work,
    #   as the two have fundamentally different behavior -- this only renames.
    # TODO: check for properly named variables?
    # TODO: double check -- what if I recurse into a region where a variable becomes free again??  I think this goes wrong
    targets = m.keys() & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be replaced.
            return TypedTerm(m[expr.op], expr.type)
        expr = expr.copy()
        if isinstance(expr.op, TypedExpr):
            expr.op = variable_convert(expr.op, m)
        for i in range(len(expr.args)):
            if isinstance(expr.args[i], TypedExpr):
                expr.args[i] = variable_convert(expr.args[i], m)
            else:
                # ???
                raise ValueError("problem during variable conversion...") # TODO: make less cryptic
    return expr

def old_variable_replace(expr, m):
    """Replace free instances of variables in expr, as determined by the map m.

    Operates on a copy.
    expr: a TypedExpr
    m: a map from strings to TypedExprs (or objects that will survive factory)."""
    # TODO: check for properly named variables?
    # TODO: double check -- what if I recurse into a region where a variable becomes free again??  I think this goes wrong
    targets = m.keys() & expr.free_variables()
    if targets:
        if expr.term() and expr.op in targets:
            # expr itself is a term to be replaced.
            return TypedExpr.factory(m[expr.op])
        expr = expr.copy()
        if isinstance(expr.op, TypedExpr):
            expr.op = variable_convert(expr.op, m)
        for i in range(len(expr.args)):
            if isinstance(expr.args[i], TypedExpr):
                expr.args[i] = variable_convert(expr.args[i], m)
            else:
                # ???
                raise ValueError("problem during variable conversion...") # TODO: make less cryptic
    return expr

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
    overlap = t.free_variables() & blocklist
    full_bl = blocklist | t.free_variables() | t.bound_variables()
    # note that this relies on the side effect of alpha_variant...
    conversions = {x : alpha_variant(x, full_bl) for x in overlap}
    return variable_convert(t, conversions)

def alpha_convert_new(t, blocklist):
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

def typed_expr_old(s):
    """Create an Expr representing a logic expression by parsing the input
    string. Symbols and numbers are automatically converted to Exprs.
    In addition you can use alternative spellings of these operators:
      'x ==> y'   parses as   (x >> y)    # Implication
      'x <== y'   parses as   (x << y)    # Reverse implication
      'x <=> y'   parses as   (x % y)     # Logical equivalence
      'x =/= y'   parses as   (x ^ y)     # Logical disequality (xor)
    But BE CAREFUL; precedence of implication is wrong. expr('P & Q ==> R & S')
    is ((P & (Q >> R)) & S); so you must use expr('(P & Q) ==> (R & S)').
    >>> expr('P <=> Q(1)')
    (P <=> Q(1))
    >>> expr('P & Q | ~R(x, F(x))')
    ((P & Q) | ~R(x, F(x)))
    """
    if isinstance(s, TypedExpr): 
        return s
    elif isinstance(s, Number): 
        return TypedExpr(s)
    elif isinstance(s, str):
        return TypedExpr.parse_expr_string(s)
    else:
        raise NotImplementedError


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
    def __init__(self, result,  desc=None, origin=None, latex_desc=None):
        self.result = result
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

    def steps_sequence(self, latex=False):
        l = list()
        if len(self.steps) > 0:
            l.append((self.steps[0].origin_str(latex), None))
            for i in range(len(self.steps)): # assume that origin matches previous result.  Could check this.
                if latex:
                    l.append((self.steps[i].result.latex_str(), self.steps[i].latex_desc))
                else:
                    l.append((repr(self.steps[i].result), self.steps[i].desc))
        return l

    def latex_steps_str(self):
        l = self.steps_sequence(latex=True)
        s = "<table>"
        i = 1
        for (expr, reason) in l:
            if reason is None:
                s += "<tr><td style=\"padding-right:5px\">%2i. </td><td style=\"padding-right:5px\">%s</td><td style=\"padding-left:10px;border-left:1px solid #848482\"></td></tr>" % (i, expr)
            else:
                s += "<tr><td style=\"padding-right:5px\">%2i. </td><td style=\"padding-right:5px\">%s</td><td style=\"padding-left:10px;border-left:1px solid #848482\">%s</td></tr>" % (i, expr, reason)
            i += 1
        s += "</table>"
        return s

    def _repr_latex_(self):
        return self.latex_steps_str()

    def steps_str(self):
        l = self.steps_sequence(latex=False)
        s = ""
        i = 1
        for (expr, reason) in l:
            if reason is None:
                s += "%2i. %s\n" % (i, expr)
            else:
                s += "%2i. %s    (%s)\n" % (i, expr, reason)
            i += 1
        return s

    def __str__(self):
        return self.steps_str()


def derivation_factory(result, desc=None, latex_desc=None, origin=None, steps=None):
    if origin is None:
        if steps is not None and len(steps) > 0:
            origin = steps[-1].result
    drv = Derivation(steps)
    # note: will make a copy of the derivation if steps is one; may be better to have something more efficient in the long run
    drv.add_step(DerivationStep(result, desc=desc, origin=origin, latex_desc=latex_desc))
    return drv

def derived(result, origin, desc=None, latex_desc=None):
    """Convenience function to return a derived TypedExpr while adding a derivational step.
    Always return result, adds or updates its derivational history as a side effect."""
    if result == origin: # may be inefficient?
        return result
    if result.derivation is None:
        d = origin.derivation
    else:
        d = result.derivation
    result.derivation = derivation_factory(result, desc=desc, latex_desc=latex_desc, origin=origin, steps=d)
    return result



test_setup()

def FA(fun, arg):
    if (not fun.type.functional()) or fun.type.left != arg.type:
        raise TypeMismatch(fun, arg, "Function Application")
    return fun(arg)

def PM(fun1, fun2):
    """H&K predicate modification -- restricted to type <et>."""
    if fun1.type != fun2.type or fun1.type != type_property:
        raise TypeMismatch(fun1, fun2, "Predicate Modification")
    varname = fun1.varname
    if fun2.varname != varname:
        # ensure that the two functions use the same variable name, by beta reduction
        #body2 = LFun(fun2.argtype, beta_reduce(fun2.body, fun2.varname, TypedTerm(varname, fun2.argtype)))
        # actually direct beta reduction isn't a good idea, because I'd have to ensure alpha conversion
        # so just apply with a new variable to get a body
        body2 = fun2.apply(TypedTerm(varname, fun2.argtype))
    else:
        # not sure this efficiency is really necessary
        body2 = fun2.body
    return LFun(fun1.argtype, fun1.body & body2, fun1.varname)



# def setup():
#     hk = HK()
#     prop = FunType(hk.e,hk.t)
#     print(prop)
#     print(hk.hastype(prop))
#     testf = LFun(prop, hk.t, "x is a cat")
#     print(testf)



