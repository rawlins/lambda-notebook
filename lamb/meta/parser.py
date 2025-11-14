import sys, re, traceback, collections, enum, typing, dataclasses, string

from enum import StrEnum
from dataclasses import dataclass, field

from lamb.parsing import ParseError
from lamb.parsing import Parselet, REParselet, Label, Optional, Precondition
from lamb.parsing import ASTNode, Unit, Token, Sequence, astclass, Whitespace, Join
from lamb.parsing import LeftRecursive, Repeat, LateDisjunctive, parse_error_wrap
from lamb.parsing import Failure
from lamb.types import TypeConstructor, TypeParseError

from lamb.meta.core import Language, get_type_system, get_language, subassignment
from lamb.meta.core import TypedExpr, Tuple, MapFun


def slang(l):
    if l is None:
        return get_language()
    else:
        return l


class Expr(StrEnum):
    EXPR = "expr"
    TUPLE = "tuple"
    SET = "set"
    MAP = "map"
    DOT = "dot"
    INDEX = "index"
    APPLY = "apply"
    FACTOR = "factor"
    BINDEXPR = "bindexpr"
    OPEXPR = "opexpr"
    TERM = "term"


class Attr(StrEnum):
    OP = "op"
    NAME = "name"
    ATTR = "attr"
    ARGS = "args"
    VARS = "vars"
    RESTRICTOR = "restrictor"
    TYPE = "type"


@astclass(label=Expr.EXPR)
class ExprAST(ASTNode):
    pass


@astclass(label=Attr.ARGS)
class ExprSeq(ASTNode):
    def instantiate(self, **kwargs):
        # TODO: len(0) => Tuple() case is currently special cased in ApplyAST
        return [v.instantiate(**kwargs) for v in self.children]


@astclass(label=Expr.TUPLE)
class TupleAST(ASTNode):
    def instantiate(self, **kwargs):
        return TypedExpr.factory(
            tuple(v.instantiate(**kwargs) for v in self.children),
               **kwargs)


@astclass(label=Expr.SET)
class SetAST(ASTNode):
    def instantiate(self, **kwargs):
        # TODO dbl check order...
        return TypedExpr.factory(
            set([v.instantiate(**kwargs) for v in self.children]),
               **kwargs)


@astclass(label=Expr.MAP)
class MapAST(ASTNode):
    def instantiate(self, **kwargs):
        if len(self.children) % 2 == 1:
            raise ParseError(f"AST error: odd-length AST for map", s=self.s, i=self.i)
        if len(self.children) == 0:
            # TODO: remove hardcoding for this case
            return MapFun()
        return TypedExpr.factory(
            {self.children[i].instantiate(**kwargs):self.children[i+1].instantiate(**kwargs)
                         for i in range(0, len(self.children), 2)},
            **kwargs)



@astclass(label=Attr.VARS)
class VarSeq(ExprSeq):
    def ensure_types(self, language):
        for i in range(len(self.children)):
            if self.children[i].type is None:
                # XX reconcile with call to `default_type` in TypedTerm constructor
                # Also, check strict type setting
                self.children[i] = TermNode(self.children[i].name,
                                        slang(language).default_type(self.children[i].name))

    @classmethod
    def from_ast(cls, a):
        return cls.seq_from_ast(a, ast_constraint=TermNode)


# binary operator expressions
@astclass(label=Expr.OPEXPR)
class OpExprAST(ASTNode):
    op: str
    op_i = None
    def instantiate(self, language=None, **kwargs):
        if not slang(language).is_op_symbol(self.op):
            raise ParseError(f"Unknown operator `{self.op}`", s=self.s, i=self.op_i)
        # TODO: validating ops against the registry doesn't work quite right
        return TypedExpr.factory(self.op,
                                 *[n.instantiate(language=language, **kwargs) for n in self.children],
                                 language=language,
                                 **kwargs)

    @classmethod
    def from_ast(cls, a):
        # binary operator expressions are initially parsed with a flat AST. We need to
        # restructure according to operator precedence.
        # a version of the precedence-climbing algorithm:
        def restructure(cur, min_prec):
            result = a.children[cur - 1] # lhs
            if cur >= len(a.children):
                return result, cur
            while cur < len(a.children):
                cur_op = a.children[cur][0]
                # TODO: how to parameterize for language?
                prec = get_language().registry.precedence(cur_op)
                if prec < min_prec:
                    break

                if cur_op in get_language().registry.right_assoc:
                    next_prec = prec
                else:
                    next_prec = prec + 1 # we need to escalate precedence to loop on the recursive call
                # trivial recursion + looping = left association
                # non-trivial recursion = right association
                # note: iteration happens here!
                op_i = a.children[cur].i
                right, cur = restructure(cur + 2, next_prec)
                # TODO: remove
                result = OpExprAST(op=cur_op, children=[result, right], state=result.state)
                result.op_i = op_i
            return result, cur
        result, _ = restructure(1, 1)
        return result


# prefix operator, symbol only. Prefix text operators use apply syntax.
@astclass(label=Expr.FACTOR)
class FactorAST(OpExprAST):
    @classmethod
    def from_ast(cls, a):
        # a `factor` is a sequence of prefix operators followed by a more
        # arbitrary expression. Restructure into a binary branching AST.
        result = a.children[-1]
        for i in range(len(a.children) - 2, -1, -1):
            result = FactorAST(op=a.children[i][0], children=[result],
                               state=a.children[i].state)
            result.op_i = a.children[i].i
        return result


#postfix operator, text only
@astclass(label=Expr.DOT)
class DotAST(ASTNode):
    attr: str
    def instantiate(self, language=None, **kwargs):
        # TODO: needs work

        # currently follows logic from facade: error unless there's a matching unary operator
        # of any kind.
        lhs = self.children[0].instantiate(language=language, **kwargs)
        matches = slang(language).registry.get_operators(arity=1, symbol=self.attr)
        if not matches:
            raise ParseError(
                f"Unknown postfix unary operator `{self.attr}` for expression type `{lhs.type}`", s=self.s, i=self.i)

        return TypedExpr.factory(self.attr, lhs, language=language, **kwargs)


# prefix function or operator
# assumption: valid alphanumeric operator names are a subset of valid term names
# this distinction is handled in instantiation, not parsing
@astclass(label=Expr.APPLY)
class ApplyAST(ASTNode):
    def instantiate(self, language=None, **kwargs):
        if len(self.children[1]) == 0:
            rhs = []
        else:
            rhs = self.children[1].instantiate(language=language, **kwargs)

        if isinstance(self.children[0], TermNode) and self.children[0].is_operator(language):
            return self.children[0].instantiate_as_operator(language, *rhs, **kwargs)

        if len(rhs) == 0:
            # 0-ary functions have the type signature <(), whatever>
            # TODO: the logic here is filling in a gap in current _construct_appl
            rhs = [Tuple()]

        return TypedExpr.factory(self.children[0].instantiate(language=language, **kwargs), *rhs, **kwargs)


@astclass(label=Expr.INDEX)
class IndexAST(ASTNode):
    def instantiate(self, **kwargs):
        return TypedExpr.factory('[]',
                                 self.children[0].instantiate(**kwargs),
                                 self.children[1].instantiate(**kwargs),
                                 **kwargs)


@astclass(label=Expr.BINDEXPR)
class BindingAST(ASTNode):
    op: str
    vars: VarSeq
    restrictor: typing.Optional[ASTNode]
    expr: ASTNode

    op_class = None

    def __post_init__(self):
        super().__post_init__()
        # TODO: parameterize by language somehow
        if self.op in get_language().registry.canonicalize_binding_ops:
            self.op = get_language().registry.canonicalize_binding_ops[self.op]
        if self.op not in get_language().registry.binding_ops:
            # should be unreachable
            raise ParseError(f"Unknown binding operator `{self.op}`", s=self.s, i=self.i)
        self.op_class = get_language().registry.binding_ops[self.op]

    def classprop(self, k, default=None):
        assert(self.op_class is not None)
        return getattr(self.op_class, k, default)

    def precheck(self, language):
        # side effect: will initialize any `None` types to the default type
        # for the variable name
        if self.vars:
            for i in range(len(self.vars)):
                if not is_var_symbol(self.vars[i].name):
                    raise ParseError(
                        f"Need variable name in binding expression `{self.op_class.canonical_name}`"
                        f" (received non-variable `{self.vars[i].name}`)", s=self.vars.s, i=self.vars.i)

            self.vars.ensure_types(language)

            if not self.classprop('allow_multivars') and len(self.vars) > 1:
                raise ParseError(
                    f"Operator class `{self.op_class.canonical_name}` does not"
                    " allow >1 variables", s=self.vars.s, i=self.vars.i)

        if not self.classprop('allow_novars') and (self.vars is None or len(self.vars) == 0):
            raise ParseError(
                f"Operator class `{self.op_class.canonical_name}` requires"
                " a variable to bind", s=self.vars.s, i=self.vars.i)

        if not self.classprop('allow_restrictor') and self.restrictor is not None:
            raise ParseError(
                f"Operator class `{self.op_class.canonical_name}` does not"
                " allow a restrictor", s=self.restrictor.s, i=self.restrictor.i)

        # note: type of restrictor not checked here! Instantiating class is
        # responsible for that.

    def get_opclass_kwargs(self, language=None, **factory_kwargs):
        from lamb.meta.core import tenorm
        kwargs = dict(assignment=factory_kwargs.get('assignment', {}))
        if self.classprop('allow_restrictor') and self.restrictor is not None:
            with parse_error_wrap("Error when trying to instantiate binding expression restrictor",
                        s=self.restrictor.s, i=self.restrictor.i):
                kwargs['restrictor'] = self.restrictor.instantiate(language=language, **factory_kwargs)
        return kwargs

    def instantiate(self, assignment=None, language=None, **kwargs):
        from lamb.meta.core import tenorm
        self.precheck(language) # validate var sequence
        # TODO: this inherits a behavior from before the parsing patch where
        # variable instantiation here just ignored the assignment. We definitely
        # don't want to *instantiate* from the assignment, but maybe we want to
        # inherit type constraints. Two cases:
        # 1. formulas like `Forall x_e : Exists x_t: P(x)` which currently
        #    parse just fine. 
        # 2. cases where the global environment has declaratively set variable
        #    types/values; the types get ignored. 
        var_arg = self.vars.instantiate(assignment=None, language=language, **kwargs)

        inst_assignment = subassignment(assignment, {v.op:v for v in var_arg})

        if not (self.classprop('allow_novars') or self.classprop('allow_multivars')):
            # constructor should take a single variable
            var_arg = var_arg[0]

        with parse_error_wrap("Error when trying to instantiate binding expression body",
                    s=self.expr.s, i=self.expr.i):
            body = self.expr.instantiate(assignment=inst_assignment, language=language, **kwargs)

        return self.op_class(var_arg, body, **self.get_opclass_kwargs(assignment=assignment, language=language, **kwargs))

    @property
    def opname(self):
        return self.op_class.__name__


# using REParselets here as a convenient package for raw+compiled regexes
base_term = REParselet(r'([\w][^\W_]*)')

# symbols cannot start with a non-alpha char. For now, text operators have
# identical constraints.
symbol_term = REParselet(r'([^\W\d][^\W_]*)')
text_op = symbol_term

glyph_op_symbols_re = r'[!@%^&*~<>|/\-=+]'
glyph_op = REParselet(fr'({glyph_op_symbols_re}+)')
glyph_op_prefix = REParselet(fr'({glyph_op_symbols_re})')

def valid_text_op(s):
    return text_op.fullmatch(s) is not None


def valid_glyph_op(s, prefix=False):
    if prefix:
        return glyph_op_prefix.fullmatch(s) is not None
    else:
        return glyph_op.fullmatch(s) is not None


def valid_op_symbol(s, prefix=False):
    # XX this relies on these two checks being disjoint
    return valid_glyph_op(s, prefix=prefix) or valid_text_op(s)


def is_symbol(s):
    """A string `s` is a symbol if it starts with an alphabetic char or `_` and
    contains only alphanumeric characters."""
    # XX is the str check really needed any more?
    return isinstance(s, str) and symbol_term.fullmatch(s) is not None


def symbol_is_var_symbol(s):
    # low cost way of checking whether something already known to be a symbol is
    # a variable. Not safe to use unless `is_symbol(s)` is True.
    return s[0].islower()


def symbol_is_constant_symbol(s):
    return not symbol_is_var_symbol(s)


def is_var_symbol(s):
    """A string s is a variable symbol if it's a symbol that starts with a
    lowercase letter."""
    return is_symbol(s) and symbol_is_var_symbol(s)


# some hardcoded cases
# build into parser directly?
fixed_constants = {
    'True': True,
    '_True': True,
    'False': False,
    '_False': False,
}


@astclass(Expr.TERM)
class TermNode(ASTNode):
    name: str
    type: typing.Optional[TypeConstructor] = None

    def is_operator(self, language):
        return slang(language).is_op_symbol(self.name)

    def instantiate_as_operator(self, language, *args, **kwargs):
        if self.type is not None and self.is_operator(language): # if the latter is true, force the internal error below
            raise ParseError(
                f"Operators cannot receive type annotations (operator `{self.name}`)",
                s=self.s, i=self.i)

        if slang(language).is_local(self.name):
            return slang(language).instantiate_local(self.name, args)
        elif slang(language).is_op_symbol(self.name):
            if len(args) == 0:
                # XX verify this is correct, and probably fix this
                args = [Tuple()]
            return TypedExpr.factory(self.name, *args, **kwargs)

        raise ParseError("Internal parser error: term instantiated as operator", s=self.s, i=self.i)

    def instantiate(self, typ=None, assignment=None, language=None, **kwargs):
        # allow a type override. Note: this is *not* cross-checked with self.type!
        # note `typ` used here for consistency with metalanguage code
        if typ is None:
            typ = self.type

        if self.is_operator(language):
            raise ParseError(
                f"Stray operator name `{self.name}` in expression", s=self.s, i=self.i)

        x = self.name
        if x == "type":
            if typ is None:
                raise ParseError(f"Stray reserved word `type` in expression", s=self.s, i=self.i)
            x = typ
            typ = None
        elif x in fixed_constants:
            x = fixed_constants[x]
        elif x[0] in string.digits:
            # TODO: currently, no floats allowed. There are potential use cases
            # in e.g. probabilistic or gradable semantics.
            try:
                x = int(x)
            except (ValueError, TypeError):
                raise ParseError(f"Invalid numeric symbol `{x}` in expression", s=self.s, i=self.i)

        return TypedExpr.term_factory(x, typ=typ,
                                        preparsed=True, assignment=assignment)


# Here begins the parser itself:


class TypeParser(Unit):
    parser = Parselet(get_type_system().type_parser_recursive, ast_label=Attr.TYPE)
    name = "type"


# currently:
# term -> "type" type
# term -> base_term ("_" type)
# however, base_term covers a bunch of ground that is implemented in instantiation,
# not parsing, including numerics and True/False.
class TermParser(Unit):
    parser = (Label(TermNode,
                Precondition(REParselet(r'(type) ', ast_label=Attr.NAME)) + TypeParser()
                | REParselet(base_term, ast_label=Attr.NAME)
                    + Optional(Precondition(REParselet('_')) + TypeParser(),
                         fully=False)))
    name = "term"

    def __init__(self, error="Expected a valid term"):
        super().__init__(error=error)

    def _parse(self, state):
        n, cur = super()._parse(state)
        if cur.e and isinstance(cur.e, ParseError) and not isinstance(cur.e, TypeParseError):
            # intercept and rewrite
            return None, self.error(state)
        return n, cur


# Binding operator parsing is packaged as a class to better encapsulate update
# behavior on changes to the list of binding operators. Basically, binding operator
# names are treated as soft keywords that can be dynamically updated.
#
# binding -> BindingOpName ",".term ":" subexpr
#
# (where BindingOpName is a list drawn from the operator registry)
# XX error messaging on typos in operator names?
class BindingParser(Unit):
    subexpr = Unit()
    name = "binding"

    @classmethod
    def update_bops(cls, reg):
        # TODO: shouldn't be a classmethod
        # TODO: the old parser allowed `λx` as a special case
        bop_names = (reg.binding_ops.keys()
                                | reg.canonicalize_binding_ops.keys())
        bop_names_re = rf'({"|".join(bop_names)})'
        cls.bop_names_re = bop_names_re
        cls.bop_parser = Token(bop_names_re, alphanum=True, ast_label=Attr.OP)
        cls.parser = None # force rebuild on next call to `parse`

    @classmethod
    def build_parser(cls):
        return (Label(BindingAST)
                   + Precondition(cls.bop_parser
                              + Label(VarSeq,
                                      Join(Token(","), TermParser(), allow_empty=True))
                              + (Label(Attr.RESTRICTOR)
                                 # XX good error messaging here is a bit tricky
                                 + Optional(Precondition(Token("<<")) + cls.subexpr, fully=False))
                              + Token(":"))
                      + cls.subexpr)


# TODO: do this in Language init?
get_language().registry.add_bop_listener(BindingParser.update_bops, initial_run=True)


class ExprParser(Unit):
    subexpr = Unit()
    name = "expr"

    @classmethod
    def build_parser(cls):
        # the following rule is built in a complex way:
        # atom -> group
        # atom -> tuple
        # atom -> set
        # atom -> map
        # atom -> term
        #
        # Rather than approaching this completely disjunctively: batch group/tuple via the
        # prefix "(", and set/map via the prefix "{". Each of these uses late disambiguation.


        # tuple -> "(" ")"
        # tuple -> "(" subexpr ",".subexpr ")"
        # group -> "(" subexpr ")"
        #
        # Anything beginning with an open paren is grouped here, using
        # LateDisjunctive (`@`) rules to disambiguate after the paren and then
        # the subexpression.
        group_or_tuple = (REParselet(r'\(\s*')
                    @ (Label(TupleAST) + Precondition(REParselet(r'\)')))
                    @ ((cls.subexpr + Whitespace())
                        @ (Label(TupleAST)
                            + Precondition(REParselet(r',\s*'))
                            + Join(Token(r','), cls.subexpr, allow_empty=True, allow_final=True)
                            + Token(r'\)', error="Expected closing `)` for tuple"))
                        @ Precondition(Token(r'\)'))) # group labeled via recursion
                    @ Failure("Following opening `(`, expected `)`-terminated group or tuple "))
        group_or_tuple.name = "()-rule"
        cls.group_or_tuple = group_or_tuple

        # set -> "{" "}"
        # map -> "{" ":" "}"
        # set -> "{" subexpr "}"
        # set -> "{" subexpr ",".subexpr "}"
        # map -> "{" subexpr ":" subexpr ",".(subexpr ":" subexpr) "}"
        #
        # use late disjuncts to progressively disambiguate following an opening
        # `{`.
        # note that unlike python, `{}` gives the empty set and `{:}` gives the empty map. 
        set_or_map = (REParselet(r'{\s*')
                        @ (Label(SetAST) + Precondition(REParselet(r'}')))
                        @ (Label(MapAST) + Precondition(REParselet(r':\s*}')))
                        @ ((cls.subexpr + Whitespace())
                            @ (Label(SetAST) + Precondition(REParselet(r'}')))
                            @ (Label(SetAST) + Precondition(REParselet(r',\s*'))
                                             + Join(Token(r','), cls.subexpr, allow_empty=True, allow_final=True)
                                             + Token(r'}', error="Expected closing `}` for set"))
                            @ (Label(MapAST) + Precondition(REParselet(r':\s*'))
                                             + cls.subexpr
                                             + Join(Token(r','),
                                                    cls.subexpr + Token(r':') + cls.subexpr,
                                                    allow_empty=True, allow_final=True, initial_join=True)
                                             + Token(r'}', error="Expected closing `}` for map")))
                        @ Failure("Following opening `{`, expected valid `}`-terminated set or map"))

        set_or_map.name = "{}-rule"
        cls.set_or_map = set_or_map

        # rule putting the pieces of `atom` together.
        atom = Unit(Unit(group_or_tuple)
                    | Unit(set_or_map)
                    | TermParser(error="Expected a valid expression"),
                    name="atom")
        cls.atom = atom

        # left-recursive rule:
        # S -> atom "." text_op
        # S -> atom "[" expr "]"
        # S -> atom "(" ",".expr ")"
        # S -> atom
        primary = LeftRecursive(
            atom,
            Label(DotAST) + (Precondition(Token(r'\.'))
                             + (Label(Attr.ATTR) + REParselet(text_op, name="postfix operator"))),
            Label(IndexAST) + (Precondition(Token(r'\[')) + cls.subexpr + Token(r'\]')),
            (Label(ApplyAST, force_node=True)
             + (Precondition(Token(r'\('))
                 + (Label(ExprSeq)
                     + Join(REParselet(r"\s*,\s*"), cls.subexpr,
                        allow_empty=True, allow_final=True, force_node=True))
                 + Token(r'\)', error="Expected closing `)` for function argument list"))),
            name="primary"
        )
        cls.primary = primary

        # factor -> SymbolOp+ primary
        # factor -> primary
        # note: factors take higher precedence than all binary operators! (Unlike python...)
        factor_op_token = Token(glyph_op_prefix.raw_regex, ast_label=Attr.OP)
        factor = (Unit(Label(FactorAST)
                      + Precondition(factor_op_token)
                          + Repeat(factor_op_token)
                          + primary)
                  | primary)

        factor.name = "factor"

        # opexpr -> SymbolOp.factor
        # (in the case of no operators, this amounts to opexpr -> factor, unlabeled)
        # note a difference from python: because symbol ops are very flexible,
        # an infix op followed by a prefix op (factor) must be separated by whitespace.
        # E.g. python parses "2 ++4" as +(2, +4), but we parse it as ++(2,4)
        # the redundant Whitespace() here is in order to ge the position right for error
        # messaging
        opexpr = Unit(Join(Token(glyph_op.raw_regex, ast_label=Attr.OP), factor,
                        ast_label=OpExprAST,
                        name="operator expression",
                        label_single=None, # without at least one op, defer label to factor
                        empty_error="Expected a valid expression"))

        # expr -> binding
        # expr -> opexpr
        parser =  Label(ExprAST, BindingParser()
                                 | opexpr)
        # complete the recursion
        BindingParser.subexpr.parser = parser
        cls.subexpr.parser = parser
        parser._repr_pretty_ = cls._repr_pretty_
        return parser


def build_expr_parser():
    rexpr = ExprParser()

    # this final wrapper enforces full string parsing
    # can anything better be done with this error message?
    return Sequence(rexpr, REParselet(r'$', error="Invalid syntax"), force_node=False)


expr_parser = build_expr_parser()
term_parser = TermParser()
type_parser = TypeParser()
