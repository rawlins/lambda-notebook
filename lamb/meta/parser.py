import sys, re, traceback, collections, enum, typing, dataclasses

try:
    EnumClass = enum.StrEnum
except:
    EnumClass = enum.Enum

from dataclasses import dataclass, field

from lamb.parsing import find_pattern_locations, consume_pattern, consume_whitespace
from lamb.parsing import consume_char, ParseError, struc_strip, flatten_paren_struc
from lamb.parsing import Parselet, REParselet, Label, Optional, Precondition, term_re
from lamb.parsing import ASTNode, Unit, Token, Sequence, astclass, Whitespace, Join
from lamb.parsing import LeftRecursive, Repeat, LateDisjunctive
from lamb.types import TypeConstructor

from lamb.meta.core import get_type_system, registry, subassignment
from lamb.meta.core import is_op_symbol, TypedExpr, Tuple, MapFun


class Expr(EnumClass):
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


class Attr(EnumClass):
    OP = "op"
    NAME = "name"
    ATTR = "attr"
    ARGS = "args"
    VARS = "vars"
    RESTRICTOR = "restrictor"
    TYPE = "type"


# XX move the precedence stuff into the registry
# XX allow for operators to disable associativity, i.e. require parens
op_precedence = {
    '**': 8,
    '*': 7,
    '/': 7,
    '@': 7,
    '%': 7, # XX revisit
    '+': 6,
    '-': 6,
    '<<': 5, # XX revisit
    '==': 5,
    '<=>': 5,
    '!=': 5,
    '^': 5, # XX revisit
    '<': 5,
    '>': 5,
    '<=': 5,
    '>=': 5,
    '&': 4,
    '|': 3,
    '>>': 2, # XX revisit
    '=>': 2,
}

# `p >> q | r` = `p >> (q | r)`
# `p >> q & r` = `p >> (q & r)`
# `p | q >> r` = `(p | q) >> r`
# `p & q >> r` = `(p & q) >> r`
# `p <=> q >> r` = `(p <=> q) >> r`
# `p >> q <=> r` = `p >> (q <=> r)`


def precedence(op):
    if op in op_precedence:
        return op_precedence[op]
    elif op[0] in op_precedence:
        return op_precedence[op[0]]
    else:
        return 9


# left associative is the default
right_assoc = {'**'}



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
    def ensure_types(self):
        from lamb.meta.core import default_variable_type
        for i in range(len(self.children)):
            if self.children[i].type is None:
                self.children[i] = TermNode(self.children[i].name,
                                          default_variable_type(self.children[i].name))

    @classmethod
    def from_ast(cls, a):
        return cls.seq_from_ast(a, ast_constraint=TermNode)


# binary operator expressions
@astclass(label=Expr.OPEXPR)
class OpExprAST(ASTNode):
    op: str
    op_i = None
    def instantiate(self, **kwargs):
        if not is_op_symbol(self.op):
            raise ParseError(f"Unknown operator `{self.op}`", s=self.s, i=self.op_i)
        # TODO: validating ops against the registry doesn't work quite right
        return TypedExpr.factory(self.op,
                                 *[n.instantiate(**kwargs) for n in self.children],
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
                prec = precedence(cur_op)
                if prec < min_prec:
                    break

                if cur_op in right_assoc:
                    next_prec = prec
                else:
                    next_prec = prec + 1 # we need to escalate precedence to loop on the recursive call
                # trivial recursion + looping = left association
                # non-trivial recursion = right association
                # note: iteration happens here!
                op_i = a.children[cur].i
                right, cur = restructure(cur + 2, next_prec)
                # TODO: remove
                from .core import builtin_op_aliases
                if cur_op in builtin_op_aliases:
                    cur_op = builtin_op_aliases[cur_op]
                result = OpExprAST(op=cur_op, children=[result, right], s=result.s, i=result.i)
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
                               s=a.children[i].s, i=a.children[i].i)
            result.op_i = a.children[i].i
        return result


#postfix operator, text only
@astclass(label=Expr.DOT)
class DotAST(ASTNode):
    attr: str
    def instantiate(self, **kwargs):
        global registry
        # TODO: needs work

        # currently follows logic from facade: error unless there's a matching unary operator
        # of any kind.
        lhs = self.children[0].instantiate(**kwargs)
        matches = registry.get_operators(arity=1, symbol=self.attr)
        if not matches:
            raise ParseError(
                f"Unknown postfix unary operator `{self.attr}` for expression type `{lhs.type}`", s=self.s, i=self.i)

        return TypedExpr.factory(self.attr, lhs, **kwargs)


# prefix function or operator
# assumption: valid alphanumeric operator names are a subset of valid term names
# this distinciton is handled in instantiation, not parsing
@astclass(label=Expr.APPLY)
class ApplyAST(ASTNode):
    def instantiate(self, **kwargs):
        if isinstance(self.children[0], TermNode):
            left_name = self.children[0].name
        else:
            left_name = None
        is_local = left_name and self.children[0].name in TypedExpr._parsing_locals

        if len(self.children[1]) == 0:
            if is_local:
                rhs = []
            else:
                # 0-ary functions have the type signature <(), whatever>
                # TODO: the logic here is filling in a gap in current _construct_appl
                rhs = [Tuple()]
        else:
            rhs = self.children[1].instantiate(**kwargs)

        from lamb.meta.core import is_op_symbol
        left = None
        if left_name:
            # XX remove somehow
            if is_op_symbol(left_name):
                if self.children[0].type is not None:
                    raise ParseError(
                        f"Syntax error: operators cannot receive type annotations (operator `{self.children[0].name}`)",
                        s=self.children[0].s, i=self.children[0].i)
                left = left_name
            elif is_local:
                # legacy case: locals that are not operator symbols
                # XX probably this currently shadows the next branch
                if self.children[0].type is not None:
                    raise ParseError(
                        f"Syntax error: operators cannot receive type annotations (operator function `{self.children[0].name}`)",
                        s=self.children[0].s, i=self.children[0].i)
                return TypedExpr._parsing_locals[left_name](rhs)

        if left is None:
            left = self.children[0].instantiate(**kwargs)
        return TypedExpr.factory(left, *rhs, **kwargs)


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
        global registry
        super().__post_init__()
        if self.op in registry.canonicalize_binding_ops:
            self.op = registry.canonicalize_binding_ops[self.op]
        if self.op not in registry.binding_ops:
            # should be unreachable
            raise ParseError(f"Unknown binding operator `{self.op}`", s=self.s, i=self.i)
        self.op_class = registry.binding_ops[self.op]

    def classprop(self, k, default=None):
        assert(self.op_class is not None)
        return getattr(self.op_class, k, default)

    def precheck(self):
        # side effect: will initialize any `None` types to the default type
        # for the variable name
        from lamb.meta.core import is_var_symbol
        if self.vars:
            for i in range(len(self.vars)):
                if not is_var_symbol(self.vars[i].name):
                    raise ParseError(
                        f"Need variable name in binding expression `{self.op_class.canonical_name}`"
                        f" (received non-variable `{self.vars[i].name}`)", s=self.vars.s, i=self.vars.i)

            self.vars.ensure_types()

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

    def get_opclass_kwargs(self, **factory_kwargs):
        from lamb.meta.core import tenorm
        kwargs = dict(assignment=factory_kwargs.get('assignment', {}))
        if self.classprop('allow_restrictor') and self.restrictor is not None:
            kwargs['restrictor'] = tenorm(self.restrictor.instantiate(**factory_kwargs))
        return kwargs

    def instantiate(self, assignment=None, **kwargs):
        from lamb.meta.core import tenorm
        self.precheck() # validate var sequence
        # TODO: this inherits a behavior from before the parsing patch where
        # variable instantiation here just ignored the assignment. We definitely
        # don't want to *instantiate* from the assignment, but maybe we want to
        # inherit type constraints. Two cases:
        # 1. formulas like `Forall x_e : Exists x_t: P(x)` which currently
        #    parse just fine. 
        # 2. cases where the global environment has declaratively set variable
        #    types/values; the types get ignored. 
        var_arg = self.vars.instantiate(assignment=None, **kwargs)

        inst_assignment = subassignment(assignment, {v.op:v for v in var_arg})

        if not (self.classprop('allow_novars') or self.classprop('allow_multivars')):
            # constructor should take a single variable
            var_arg = var_arg[0]

        body = tenorm(self.expr.instantiate(assignment=inst_assignment, **kwargs))

        return self.op_class(var_arg, body, **self.get_opclass_kwargs(assignment=assignment, **kwargs))

    @property
    def opname(self):
        return self.op_class.__name__


term_symbols_re = r'[a-zA-Z0-9]'
base_term_re = fr'{term_symbols_re}+'
full_term_re = fr'(_?{base_term_re})(_)?'
match_term_re = fr'{base_term_re}$'

# text operator symbols cannot start with a non-alpha char
text_op_re = r'([^\W\d]\w*)'
symbol_op_symbols_re = r'[!@%^&*~<>|\\/\-=+]'
symbol_op_re = fr'({symbol_op_symbols_re}+)'


def valid_text_op(s):
    return re.fullmatch(text_op_re, s) is not None


def valid_symbol_op(s):
    return re.fullmatch(symbol_op_re, s) is not None


def valid_op_symbol(s):
    # XX is_op vs valid...
    return is_op_symbol(s) or valid_text_op(s)


def find_term_locations(s, i=0):
    """Find locations in a string `s` that are term names."""
    # TODO: code dup with parse_term
    term_re = re.compile(full_term_re)
    unfiltered_result = find_pattern_locations(term_re, s, i=i, end=None)
    result = list()
    for r in unfiltered_result:
        if r.start() > 0 and s[r.start() - 1] == ".":
            # result is prefaced by a ".", and therefore is a functional
            # call or attribute
            continue
        result.append(r)
    return result


@astclass(Expr.TERM)
class TermNode(ASTNode):
    name: str
    type: typing.Optional[TypeConstructor] = None

    def instantiate(self, typ=None, assignment=None):
        # note `typ` used here for consistency with metalanguage code
        if typ is None:
            typ = self.type
        return TypedExpr.term_factory(self.name, typ=typ,
                                    preparsed=True, assignment=assignment)


# Here begins the parser itself:


class TypeParser(Unit):
    parser = Parselet(get_type_system().type_parser_recursive, ast_label=Attr.TYPE)


class TermParser(Unit):
    parser = (Label(TermNode)
               + REParselet(term_re, ast_label='name')
               + Optional(Precondition(REParselet('_', consume=True)) + TypeParser(),
                         fully=False))

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

    @classmethod
    def update_bops(cls, reg):
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


registry.add_bop_listener(BindingParser.update_bops, initial_run=True)


class ExprParser(Unit):
    subexpr = Unit()

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


        # tuple -> "(" subexpr ",".subexpr ")"
        # group -> "(" subexpr ")"
        # tuple -> "(" ")"
        #
        # use a "," to disambiguate between group vs tuple. Empty tuple handled as a special case.
        group_or_tuple = (((REParselet(r'\(\s*') + cls.subexpr + Whitespace()) # labeled via recursion
                              @ (Label(TupleAST, defer=True)
                                 + Precondition(REParselet(r',\s*'))
                                     + Join(Token(r','), cls.subexpr, allow_empty=True, allow_final=True)
                                     + Token(r'\)', error="Missing closing `)` for tuple"))
                              @ Token(r'\)', error="Missing closing `)`"))
                          | Label(TupleAST) + Precondition(REParselet(r'\(\s*')) + REParselet(r'\)', consume=True, error="Missing closing `)`")
                         )

        # set -> "{" subexpr "}"
        # set -> "{" subexpr ",".subexpr "}"
        # map -> "{" subexpr ":" subexpr ",".(subexpr ":" subexpr) "}"
        # map -> "{" ":" "}"
        # set -> "{" "}"
        #
        # use "," and ":" to disambiguate between set and map. empty set, empty map, singleton set handled as a special cases.
        # note that unlike python, `{}` gives the empty set and `{:}` gives the empty map. 
        set_or_map = (((REParselet(r'{\s*') + cls.subexpr + Whitespace())
                            @ (Label(SetAST, defer=True) + Precondition(REParselet(r'}', error="Missing closing `}` for set")))
                            @ (Label(SetAST, defer=True)
                               + Precondition(REParselet(r',\s*'))
                                   + Join(Token(r','), cls.subexpr, allow_empty=True, allow_final=True)
                                   + Token(r'}', error="Missing closing `}` for set"))
                            @ (Label(MapAST, defer=True)
                               + Precondition(REParselet(r':\s*'))
                                   + cls.subexpr
                                   + Join(Token(r','),
                                          cls.subexpr + Token(r':') + cls.subexpr,
                                          allow_empty=True, allow_final=True, initial_join=True)
                                   + Token(r'}', error="Missing closing `}` for map")))
                       | (Label(MapAST) + Precondition(REParselet(r'{\s*:\s*'))
                                            + REParselet(r'}', consume=True, error="Missing closing `}` for map"))
                       | (Label(SetAST) + Precondition(REParselet(r'{\s*'))
                                            + REParselet(r'}', consume=True, error="Missing closing `}` for set"))
                      )

        # rule putting the pieces of `atom` together.
        atom = Unit(Unit(group_or_tuple)
                    | Unit(set_or_map)
                    | TermParser())

        # left-recursive rule:
        # S -> atom "." text_op
        # S -> atom "[" expr "]"
        # S -> atom "(" ",".expr ")"
        # S -> atom
        primary = LeftRecursive(
            atom,
            Label(DotAST, defer=True) + (Precondition(Token(r'\.')) + (Label(Attr.ATTR) + REParselet(text_op_re))),
            Label(IndexAST, defer=True) + (Precondition(Token(r'\[')) + cls.subexpr + Token(r'\]')),
            (Label(ApplyAST, force_node=True, defer=True)
             + (Precondition(Token(r'\('))
                 + (Label(ExprSeq)
                     + Join(REParselet(r"\s*,\s*"), cls.subexpr,
                        allow_empty=True, allow_final=True, force_node=True))
                 + Token(r'\)', error="Missing closing `)` for function argument list")))
        )

        # factor -> SymbolOp+ primary
        # factor -> primary
        # note: factors take higher precedence than all binary operators! (Unlike python...)
        factor_op_token = Token(fr'({symbol_op_symbols_re})', ast_label=Attr.OP)
        factor = (Unit(Label(FactorAST)
                      + Precondition(factor_op_token)
                          + Repeat(factor_op_token)
                          + primary)
                  | primary)

        # opexpr -> SymbolOp.factor
        # (in the case of no operators, this amounts to opexpr -> factor, unlabeled)
        # note a difference from python: because symbol ops are very flexible,
        # an infix op followed by a prefix op (factor) must be separated by whitespace.
        # E.g. python parses "2 ++4" as +(2, +4), but we parse it as ++(2,4)
        # the redundant Whitespace() here is in order to ge the position right for error
        # messaging
        opexpr = Unit(Join(Token(fr'({symbol_op_re})', ast_label=Attr.OP), factor,
                        ast_label=OpExprAST,
                        label_single=None, # 
                        allow_empty=False))

        # expr -> binding
        # expr -> opexpr
        parser =  Label(ExprAST, BindingParser()
                                 | opexpr)
        # complete the recursion
        BindingParser.subexpr.parser = parser
        cls.subexpr.parser = parser
        return parser


def build_expr_parser():
    rexpr = ExprParser()

    # this final wrapper enforces full string parsing
    # can anything better be done with this error message?
    return Sequence(rexpr, REParselet(r'$', error="Invalid syntax"), force_node=False)


expr_parser = build_expr_parser()


# legacy code:
type_parser = TypeParser()
term_parser = TermParser()


def parse_term(s, i=0, return_obj=True, assignment=None):
    """Parse position `i` in `s` as a term expression.  A term expression
    is some alphanumeric sequence followed optionally by an underscore and
    a type.  If a type is not specified locally, but is present in 
    `assignment`, use that.  If a type is specified and is present in
    `assignment`, check type compatibility immediately."""
    try:
        ast, new_i = term_parser.parse(s, i=i)
        match ast:
            case TermNode(name=name, type=type):
                if return_obj:
                    return ast.instantiate(assignment=assignment), new_i
                else:
                    return name, type, new_i
            case _:
                pass
    except ParseError:
        pass

    # failure case:
    if return_obj:
        return (None, i)
    else:
        return (None, None, i)



def try_parse_term_sequence(s, lower_bound=1, upper_bound=None,
                                                    assignment=None):
    """Try to parse `s` as a sequence of terms separated by commas. This
    consumes the entire string."""
    if not isinstance(s, str):
        s = struc_strip(s)
        if len(s) > 1:
            raise ParseError(f"Unparsable extraneous material in term sequence",
                s=flatten_paren_struc(s), i=0,
                met_preconditions=True)
        s = s[0]
        if not isinstance(s, str):
            s = debracket(s)
            if len(s) == 0:
                s = ""
            elif len(s) == 1:
                s = s[0]
            else:
                raise ParseError(f"Unparsable extraneous material in term sequence",
                    s=flatten_paren_struc(s), i=0,
                    met_preconditions=True)

            if not isinstance(s, str):
                raise ParseError(f"Extraneous parentheses in term sequence",
                    s=flatten_paren_struc(s), i=0,
                    met_preconditions=True)
    s = s.strip()
    if len(s) == 0:
        sequence = list()
        i = 0
    else:
        v, typ, i = parse_term(s, i=0, return_obj=False,
                                                    assignment=assignment)
        sequence = [(v, typ)]
    if i < len(s):
        i = consume_whitespace(s, i)
        if i < len(s) and v is None:
            raise ParseError(f"Extraneous character at beginning of term sequence (`{s[i]}`)",
                s=s, i=i, met_preconditions=True)
        while i < len(s):
            i = consume_char(s, i, ",", f"expected comma in variable sequence, found `{s[i]}`")
            i = consume_whitespace(s, i)
            v, typ, i = parse_term(s, i=i, return_obj=False,
                                                    assignment=assignment)
            if v is None:
                raise ParseError(
                    "Failed to find term following comma in variable sequence",
                    s=s, i=i, met_preconditions=True)
            sequence.append((v, typ))

    if lower_bound and len(sequence) < lower_bound:
        if lower_bound == 1 and upper_bound == 1:
            err = "Expected a variable"
        else:
            err = f"Too few variables ({len(sequence)} < {lower_bound}) in variable sequence"
        raise ParseError(err, s=s, i=i, met_preconditions=True)

    if upper_bound and len(sequence) > upper_bound:
        if upper_bound == 1:
            err = "Expected a single variable, got a sequence"
        else:
            err = f"Too many variables ({len(sequence)} > {upper_bound}) in variable sequence"
        raise ParseError(err, s=s, i=i, met_preconditions=True)
    return sequence


def try_parse_typed_term(s, assignment=None):
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

    seq = try_parse_term_sequence(s, lower_bound=1, upper_bound=1,
                                                    assignment=assignment)
    return seq[0]
