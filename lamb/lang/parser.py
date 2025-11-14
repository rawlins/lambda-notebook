import enum, dataclasses, typing

from dataclasses import field
from enum import StrEnum

import lamb.parsing
from lamb.parsing import logger, remove_comments
from lamb.parsing import error_manager, parse_error_wrap, under_assignment, te_only
from lamb.parsing import ASTNode, Unit, Whitespace, REParselet, Precondition
from lamb.parsing import Keyword, Label, astclass

import lamb.meta
from lamb.meta import te, get_language
from lamb.meta.core import op_from_te
from lamb.meta.parser import term_parser, TermNode, valid_op_symbol

from .composition import Item, Items, get_system


eq_transforms = None


def init_transforms():
    global eq_transforms
    eq_transforms = {}
    eq_transforms['reduce'] = lambda x: x.reduce_all()


init_transforms()


def parse_right(left_s, right_s, env, constants=False):
    right_side = None
    with error_manager():
        with parse_error_wrap(f"Parsing of assignment to `{left_s}` failed"):
            right_side = te(right_s.strip(), assignment=env, let=True)
            if right_side is None:
                raise ParseError(f"Typed expression failed to parse in assignment to `{left_s}`", right_s.strip())
            right_side = right_side.regularize_type_env(env, constants=constants)
            right_side = under_assignment(right_side, env)
            right_side = right_side.simplify_all(reduce=True)
            return right_side
    return None


def apply_rs_transform(right_side, transform, transforms=None):
    if transforms is None:
        transforms = {}
    if transform and transform in transforms:
        transform = transforms[transform]
    elif transform is None and "default" in transforms:
        transform = transforms["default"]
    # intentional: `<>` leads to `transform=""` and prevents a transform
    if transform:
        right_side = transform(right_side).simplify_all(reduce=True)
    return right_side


class Statement(StrEnum):
    ASSIGNMENT = "assignment"
    VAR_ASSIGN = "var_assign"
    LEX_ASSIGN = "lex_assign"
    OP_ASSIGN = "op_assign"


class Attr(StrEnum):
    OP = "op"
    ARITY = "arity"
    NAME = "name"
    INDEX = "index"
    REMAINDER = "expr" # placeholder while expr parsing is not implemented
    TRANSFORM = "transform"


# overmatches relative to valid term names
term_re = r'_?[a-zA-Z0-9]+'
op_re = r'[!@%^&*~<>|\\/\-=+]+'
term_or_op_re = fr'({term_re}|{op_re})'


@astclass(None)
class AssignmentAST(ASTNode):
    expr: str # eventually, ASTNode
    transform: typing.Optional[str] = field(default=None, kw_only=True)

    def eval_right_side(self, var_env, transforms):
        # XX parameterize by language
        right_side = parse_right(self.left_desc(), self.expr, var_env, constants=True)
        if right_side is not None:
            right_side = apply_rs_transform(right_side, self.transform, transforms=transforms)
        return right_side


@astclass(Statement.VAR_ASSIGN)
class VarAssignAST(AssignmentAST):
    term: ASTNode # really, TermNode

    def left_desc(self):
        return self.term.name

    def instantiate(self, var_env, transforms, language):
        right_side = self.eval_right_side(var_env, transforms)
        if right_side is None:
            return None, None
        # if left_type is specified it, unify with right_side's
        # type, and use that for the resulting term
        left_type = self.term.type
        if left_type is None:
            left_type = right_side.type
        if left_type != right_side.type:
            right_side = right_side.ensure_typed_expr(right_side, typ=left_type)
        term = self.term.instantiate(typ=right_side.type, language=language)
        return term.op, right_side


@astclass(Statement.LEX_ASSIGN)
class LexAssignAST(AssignmentAST):
    name: str
    index: typing.Optional[str] = None

    def left_desc(self):
        return f"||{self.name}||"

    def get_index(self, env, ambiguity):
        if not self.index or self.index == "*":
            if (self.name in env and (ambiguity or self.index == "*")):
                return True
            else:
                return None # replace existing item or add a new one
        else:
            return int(self.index)

    def instantiate(self, var_env, transforms, language):
        right_side = self.eval_right_side(var_env, transforms)
        if right_side is None:
            return None

        lex_name = self.name.replace(" ", "_")
        if lex_name != self.name:
            logger().info(f"Exporting item `||{self.name}||` to python variable `{lex_name}`.")
            self.name = lex_name # side effect
        return Item(lex_name, right_side)


@astclass(Statement.OP_ASSIGN)
class OpAssignAST(AssignmentAST):
    op: str
    index: typing.Optional[str] = None
    arity: typing.Optional[str] = None

    def left_desc(self):
        return f"operator {self.op}"

    def instantiate(self, var_env, transforms, language):
        raise NotImplementedError()


class AssignmentParser(Unit):
    @classmethod
    def build_parser(cls):
        # TODO: use parser.expr_parser to directly parse right side?

        eq_parser = (Whitespace()
                     + REParselet(r'=(?:<([a-zA-Z0-9_]*)>)?',
                          ast_label=Attr.TRANSFORM,
                          error="Missing `=` in assignment")
                     + Whitespace())

        op_assign_parser = (Label(OpAssignAST)
             + Precondition(Keyword('operator', error="Missing `operator` prefix"))
             + Whitespace()
             + REParselet(term_or_op_re, ast_label=Attr.OP)
             + Whitespace()
             + REParselet(r'(?:\((\d+)\))?', ast_label=Attr.ARITY)
             + eq_parser
             + REParselet(r'.*', ast_label=Attr.REMAINDER))

        lex_assign_parser = (
            Label(LexAssignAST)
            + Precondition(REParselet(r'\|\|', error="Missing interpretation brackets"))
            + REParselet(r'[a-zA-Z _]+[a-zA-Z0-9 _]*', ast_label=Attr.NAME)
            + REParselet(r'(?:\[(-?[0-9]+|\*)\])?\|\|', ast_label=Attr.INDEX, error='error in lexical entry name')
            + eq_parser
            + REParselet(r'.*', ast_label=Attr.REMAINDER))

        var_assign_parser = (
            Label(VarAssignAST)
            + term_parser
            + eq_parser
            + REParselet(r'.*', ast_label=Attr.REMAINDER))

        return Label(Statement.ASSIGNMENT, op_assign_parser
                                                    | lex_assign_parser
                                                    | var_assign_parser)


assign_parser = AssignmentParser()


def insert_item(item, index, env):
    # TODO: should this be a Lexicon member function?
    lex_name = item.name
    if index is not None:
        if lex_name in env:
            if isinstance(env[lex_name], Items):
                l = env[lex_name]
            else:
                l = Items([env[lex_name]])
        else:
            l = Items([])
        if index is True:
            l.add_result(item)
        else:
            l[index] = item # may throw an exception
        if len(l) > 1:
            # only keep the Items object if it's actually non-trivial
            item = l
    env[lex_name] = item


def parse_assignment(s, i=0, env=None, transforms=None, ambiguity=False):
    if env is None:
        env = {}
    var_env = te_only(env)
    raw_ast, _ = assign_parser.parse(s, i=i)
    match raw_ast:
        case ASTNode(Statement.ASSIGNMENT, [VarAssignAST() | OpAssignAST()]):
            pass
        case ASTNode(Statement.ASSIGNMENT, [LexAssignAST()]):
            a_ctl = get_system().assign_controller
            default = a_ctl.default()
            var_env = default.new_child(var_env)
        case ASTNode(Statement.ASSIGNMENT):
            raise ParseError(f"Unknown assignment type `{ast.children}`", s=s, i=i)
        case _:
            raise ParseError(f"Unknown statement type `{ast.label}`", s=s, i=i)

    ast = raw_ast[0]
    left_desc = ast.left_desc()
    with parse_error_wrap(f"Assignment to `{left_desc}` failed"):
        match ast:
            case VarAssignAST():
                term_name, right_side = ast.instantiate(var_env, transforms, get_language())
                if term_name is None:
                    return ({}, env)
                else:
                    # # NOTE side-effect here
                    env[term_name] = right_side
                    return ({term_name : right_side}, env)
            case LexAssignAST():
                item = ast.instantiate(var_env, transforms, get_language())
                if item is None:
                    return {}, env
                try:
                    insert_item(item, ast.get_index(env, ambiguity), env)
                except IndexError:
                    raise ParseError(f"Invalid index `{ast.index}` in assignment to lexical entry `{left_desc}`", s=ast.s, i=ast.i)
                return {item.name: env[item.name]}, env
            case OpAssignAST(op=op_symbol, arity=arity):
                right_side = ast.eval_right_side(var_env, transforms)
                if right_side is None:
                    return {}, env

                if not valid_op_symbol(op_symbol):
                    err_ast = raw_ast[0].map[Attr.OP]
                    raise ParseError(f"Invalid operator symbol `{op_symbol}`", s=err_ast.s, i=err_ast.i)
                if arity is not None:
                    arity = int(arity)
                op_cls = op_from_te(op_symbol, right_side, arity=arity)
                get_language().registry.add_operator(op_cls)
                op = get_language().registry.get_operators(cls=op_cls)[0]
                try:
                    # operators aren't stored in the env, so attempt to display them
                    # now (TODO: sequencing will be wrong)
                    from IPython.display import display
                    display(op)
                except ImportError:
                    pass

                # XX maybe store new operators as global state somehow, for easier access?
                return ({}, env)
            case _:
                raise ParseError(f"Unknown assignment type: {raw_ast}", s=raw_ast.s, i=raw_ast.i)
    return ({}, env)


def parse_line(s, env=None, transforms=None, ambiguity=False):
    if env is None:
        env = dict()
    with error_manager(summary="Metalanguage parsing failed with exception:"):
        s = remove_comments(s)
        if len(s.strip()) > 0:
            return parse_assignment(s, transforms=transforms,
                                                env=env, ambiguity=ambiguity)
        # otherwise, only a comment on this line, fall through to a noop
        
    return ({}, env)


def parse_lines(s, env=None, transforms=None, ambiguity=False):
    if env is None:
        env = {}
    global eq_transforms
    if transforms is None:
        transforms = eq_transforms
    accum = {}
    lines = s.splitlines()
    for l in lines:
        (a, env) = parse_line(l, transforms=transforms, env=env,
                                                        ambiguity=ambiguity)
        accum.update(a)
    return (accum, env)


def parse(s, state=None, transforms=None, ambiguity=False):
    global eq_transforms
    if transforms is None:
        transforms = eq_transforms
    return parse_lines(s, transforms=transforms, env=state, ambiguity=ambiguity)
