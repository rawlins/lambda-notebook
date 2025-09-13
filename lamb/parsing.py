import sys, re, traceback, collections, enum
from contextlib import contextmanager

# imported by meta
from lamb import utils
from lamb.utils import * # TODO: remove
from lamb.display import assignment_repr

Tree = utils.get_tree_class()

global eq_transforms
eq_transforms = dict()
eq_transforms['reduce'] = lambda x: x.reduce_all()

# wrap some common circular import cases:
def logger():
    from lamb.meta import logger
    return logger

def is_te(x):
    from lamb.meta import is_te
    return is_te(x)

class ParseError(Exception):
    def __init__(self, msg, s=None, i=None, met_preconditions=True, e=None):
        self.s = s
        self.i = i
        if e:
            if isinstance(e, ParseError) and e.e:
                self.e = e.e
            else:
                self.e = e
        else:
            self.e = None
        self.msg = msg
        # set to False to indicate that a try_parse function did not find
        # preconditions for what it is supposed to consume
        self.met_preconditions = met_preconditions
        self.has_note = False

    def _try_add_note(self):
        if self.has_note or self.i is None:
            return
        try:
            self.add_note(utils.error_pos_str(self.s, self.i, prefix="  ",
                                    plain=True, multiline=True))
            self.has_note = True
        except AttributeError:
            # < python 3.11
            pass

    def _aux_str(self, plain=True):
        if self.e is None:
            return ""

        newline = False
        if (isinstance(self.e, SyntaxError)):
            # SyntaxError's full str representation is not helpful when
            # generated from an eval, so just show the message
            e_str = str(self.e.msg)
        else:
            if plain:
                e_str = str(self.e)
            else:
                e_str = None
                try:
                    e_str = self.e._repr_markdown_()
                    newline = True
                except AttributeError:
                    pass
                if not e_str:
                    e_str = str(self.e)
                    newline = True

        if newline:
            sep = plain and "\n" or "<br />&nbsp;&nbsp;&nbsp;&nbsp;"
        else:
            sep = ": "
        return sep + e_str

    def tostring(self, multiline=True, classname=True, allow_note=False):
        # include this in `prefix` so it is counted for positioning an error
        # marker
        if allow_note:
            self._try_add_note()
        if classname:
            m = f"{self.__class__.__name__}: {self.msg}"
        else:
            m = self.msg
        aux = self._aux_str()
        if self.s is None:
            return m + aux
        elif self.i is None:
            s_desc = (isinstance(self.s, str) and 'string'
                or (is_te(self, s) and 'TypedExpr'
                    or 'object'))
            return f"{m}, in {s_desc} `{self.s}`{aux}"
        else:
            if allow_note and self.has_note:
                return m
            return utils.error_pos_str(self.s, self.i, prefix=m,
                                    plain=True, multiline=multiline)

    def __str__(self):
        # used in stack trace. Therefore, we don't print the classname, and
        # don't try multiline stuff directly, because the context isn't fully
        # predictable. However, in python 3.11+, use the `add_note` mechanism
        # to show multiline messaging.
        return self.tostring(classname=False, allow_note=True, multiline=False)

    def _repr_markdown_(self):
        # it's convenient to use markdown here for backticks, but colab will
        # strip out the color. So, use both red and bold.
        aux = self._aux_str(plain=False)
        # note: the case that combines an aux string and an error position is
        # relatively untested
        if self.s is None:
            m = self.msg
        elif self.i is None:
            m = f"{self.msg}, in string `{self.s}`"
        else:
            m = utils.error_pos_str(self.s, self.i, prefix=self.msg,
                                    plain=False, multiline=True)
        # it's convenient to use markdown here for backticks, but colab will
        # strip out the color. So, use both red and bold.
        return f"<span style=\"color:red\">**{self.__class__.__name__}**</span>: {m}{aux}"

    def __repr__(self):
        return self.tostring(multiline=False)

    def _repr_pretty_(self, p, cycle):
        return p.text(self.tostring())


@contextmanager
def try_parse(suppress=False):
    try:
        yield
    except ParseError as e:
        if suppress or not e.met_preconditions:
            return None
        else:
            raise e


def consume_char(s, i, match, error=None):
    if i >= len(s):
        if error is not None:
            raise ParseError(error, s=s, i=i)
        else:
            return None
    if s[i] == match:
        return i + 1
    else:
        if error is None:
            return None
        else:
            raise ParseError(error, s=s, i=i)


def consume_pattern(s, i, regex, error=None, return_match=False, **kwargs):
    if i > len(s):
        if error is not None:
            raise ParseError(error, s=s, i=i, **kwargs)
        else:
            return None
    m = re.match(regex, s[i:])
    if m:
        if return_match:
            return (m, m.end() + i)
        else:
            return (m.group(), m.end() + i)
    else:
        if error is None:
            return None, None
        else:
            raise ParseError(error, s=s, i=i, **kwargs)


# non-negative integers only
def consume_number(s, i, error=None):
    m, i = consume_pattern(s, i, r'[0-9]+', error=error)
    if m is not None:
        m = int(m)
    return m, i


def find_pattern_locations(re, s, i=0, end=None):
    matches = list()        
    next = i
    if end is None:
        end = len(s)
    while next <= end:
        search = re.search(s, pos=next, endpos=end)
        if not search:
            break
        matches.append(search)
        next = search.end() + 1
    return matches


def consume_whitespace(s, i, plus=False, error=None):
    m_group, i = consume_pattern(s, i, r'\s*', error)
    return i


class ASTNode(object):
    __match_args__ = ("label", "values")
    def __init__(self, label, *values, s=None, i=None):
        self.label = label
        self.values = values
        self.map = {v.label: v for v in values if isinstance(v, ASTNode) and v.label is not None}
        self.s = s
        self.i = i

    def get(self, x, default=None, error=None):
        if x in self.map:
            r = self.map[x]
            if isinstance(r, ASTNode) and len(r.values) == 1 and not isinstance(r.values[0], ASTNode):
                return r.values[0]
            else:
                return r

        if error:
            raise ParseError(error, s=self.s, i=self.i)
        else:
            return default

    def __getattr__(self, name):
        if name in self.map:
            return self.get(name)
        else:
            raise AttributeError(f"Unknown field `{name}` for ASTNode `{self.label}`")

    def __contains__(self, x):
        return x in self.map

    def __len__(self):
        return len(self.values)

    def __getitem__(self, i):
        return self.values[i]

    def __repr__(self):
        if not self.values and self.map:
            # if `values` is empty, try printing the map, to handle subclasses
            # that don't use `values`
            return f"({self.label}: {repr(self.map)})"
        else:
            return f"({self.label}: {', '.join(repr(v) for v in self.values)})"


ast_transforms = {}


def transform_ast(a):
    if a.label in ast_transforms:
        return ast_transforms[a.label].from_ast(a)
    else:
        return a


def ast_node(*args, **kwargs):
    return transform_ast(ASTNode(*args, **kwargs))


class Parselet(object):
    def __init__(self, parser, ast_label=None, error=None):
        self.parser = parser
        self.ast_label = ast_label
        self.error_msg = error

    def default_error(self, s, i):
        return f"Failed to parse {self.ast_label}"

    def error(self, s, i, error=None):
        if error:
            e = error
        elif self.error_msg:
            e = self.error_msg
        else:
            e = self.default_error(s, i)
        raise ParseError(e, s=s, i=i)

    def parse(self, s, i=0):
        if self.parser is None:
            # noop parse
            return (i,)
        result = self.parser(s, i)
        if result is None or result[-1] is None:
            # interpret this as a failed parse
            self.error(s, i)
        new_i = result[-1]
        result = [x for x in result[0:-1] if x is not None]
        if not result:
            # interpret this as a consumer-only parse
            return (new_i,)
        return ast_node(self.ast_label, *result, s=s, i=i), new_i

    def __call__(self, s, i):
        return self.parse(s, i)

    def __or__(self, other):
        if isinstance(self, DisjunctiveParselet):
            # left association
            self.parser.append(other)
            return self
        else:
            return DisjunctiveParselet(self, other)

    def __add__(self, other):
        if isinstance(self, SeqParselet):
            # left association
            self.parser.append(other)
            return self
        else:
            return SeqParselet(self, other, ast_label=self.ast_label)


class Label(Parselet):
    """Dummy Parselet that serves only to provide an AST label"""
    def __init__(self, ast_label, parser=None):
        super().__init__(parser, ast_label=ast_label)

    def parse(self, s, i=0):
        if self.parser is not None:
            result = self.parser.parse(s, i)
        else:
            result = super().parse(s, i=i)
        if isinstance(result[0], ASTNode):
            result[0].label = self.ast_label
        return result


class Optional(Parselet):
    def __init__(self, parser, fully=True, ast_label=None, **kwargs):
        if ast_label is None:
            ast_label = parser.ast_label
        self.fully = fully
        super().__init__(parser, ast_label=ast_label, **kwargs)

    def parse(self, s, i=0):
        try:
            return self.parser.parse(s, i)
        except ParseError as e:
            if not self.fully and e.met_preconditions:
                raise e
            else:
                # null but succesful consumer-only parse
                return (i,)


class Precondition(Parselet):
    def __init__(self, parser, ast_label=None, **kwargs):
        if ast_label is None:
            ast_label = parser.ast_label
        super().__init__(parser, ast_label=ast_label, **kwargs)

    def parse(self, s, i=0):
        try:
            return self.parser.parse(s, i)
        except ParseError as e:
            e.met_preconditions = False
            raise e


class REParselet(Parselet):
    def __init__(self, regex, consume=None, ast_label=None, flags=0, **kwargs):
        if consume is None:
            consume = not bool(ast_label)
        self.raw_regex = regex
        self.consume = consume
        regex = re.compile(regex, flags=flags)
        super().__init__(regex, ast_label=ast_label, **kwargs)

    def default_error(self, s, i):
        return f"Failed to match pattern for {self.ast_label}"

    def parse(self, s, i=0):
        m = self.parser.match(s[i:])
        if m:
            if self.consume:
                return (m.end() + i,)
            # could do something with named groups
            result = m.groups()
            if not result:
                result = (m.group(),)
            return ast_node(self.ast_label, *result, s=s, i=i), m.end() + i
        else:
            self.error(s, i)


class Keyword(REParselet):
    def __init__(self, kw, **kwargs):
        # `kw` is intended to be alphanumeric here
        # end token check: only match if we do not continue matching alphanum
        # characters next (XX op version of this?)
        regex = rf'{kw}(?![a-zA-Z0-9])'
        super().__init__(regex, **kwargs)


# XX linebreaks
def Whitespace(plus=False):
    if plus:
        return REParselet(r'\s+', consume=True, error="failed to match whitespace")
    else:
        return REParselet(r'\s*', consume=True)


class SeqParselet(Parselet):
    def __init__(self, *parsers, **kwargs):
        super().__init__(list(parsers), **kwargs)

    def parse(self, s, i=0):
        result = []
        cur = i
        for p in self.parser:
            r = p.parse(s, cur)
            cur = r[-1]
            result.extend(r[0:-1])
        if not result:
            # interpret this as a succesful consumer-only parse
            return (cur,)
        elif len(result) == 1 and not self.ast_label and isinstance(result[0], ASTNode):
            # don't add extra AST nodes for unlabeled sequences
            return result[0], cur
        else:
            return ast_node(self.ast_label, *result, s=s, i=i), cur


class DisjunctiveParselet(Parselet):
    def __init__(self, *parsers, **kwargs):
        super().__init__(list(parsers), **kwargs)

    def default_error(self, s, i):
        return f"Failed to find disjunct in `{self.ast_label}`"

    def parse(self, s, i=0):
        for p in self.parser:
            with try_parse():
                result = p.parse(s, i)
                new_i = result[-1]
                result = result[:-1]
                if not result:
                    # interpret this as a succesful consumer-only parse
                    return (new_i,)
                return ast_node(self.ast_label, *result, s=s, i=i), new_i
        self.error(s, i)


def vars_only(env):
    """Ensure that env is a 'pure' variable assignment -- exclude anything but
    TypedExprs."""
    env2 = {key: env[key] for key in env.keys() if is_te(env[key])}
    return env2


# wrap other exception types in ParseError with designated parameters
@contextmanager
def parse_error_wrap(msg, paren_struc=None, wrap_all=True, **kwargs):
    from lamb.types import TypeParseError, TypeMismatch
    try:
        yield
    except (TypeParseError, TypeMismatch) as e:
        if not wrap_all:
            raise e
        kwargs['e'] = e
        # special case this, so that the caller doesn't need to preemptively
        # flatten
        if paren_struc:
            kwargs['s'] = flatten_paren_struc(paren_struc)
        raise ParseError(msg, **kwargs).with_traceback(e.__traceback__) from None
    except ParseError as e:
        if not e.msg:
            e.msg = msg # this should essentially not trigger ever?
        if paren_struc:
            # override any provided s...
            kwargs['s'] = flatten_paren_struc(paren_struc)

        if 's' in kwargs and e.s != kwargs['s']:
            # `i` may or may not be set, but any previous `i` won't make sense
            # in the context of the updated `s`
            e.i = kwargs.get('i', None)
            e.s = kwargs['s']
        raise e


errors_raise = False


# generalized context manager for displaying lnb errors in a sensible way. Tries
# to display them, and if not, falls back on logging.
@contextmanager
def error_manager(summary=None):
    from lamb.types import TypeParseError, TypeMismatch
    from lamb.meta.meta import DomainError
    display = None
    try:
        from IPython.display import display
    except ImportError:
        pass

    try:
        try:
            yield
        except (TypeParseError,
                TypeMismatch,
                ParseError,
                DomainError) as e:
            display(e)
            if errors_raise or not display:
                raise e
    except Exception as e:
        if summary:
            logger().error(summary)
        # putting the class name may be redundant, but sometimes str doesn't
        # give it (example: `KeyError`)
        logger().error(f"[{e.__class__.__name__}] {str(e)}")
        if errors_raise:
            raise e

def magic_opt(optname, line):
    # simple and dumb, maybe improve some day
    if line.startswith(f"{optname} "):
        return (True, line[len(optname) + 1:])
    else:
        return (False, line)


def parse_te(line, env=None, use_env=False):
    # implementation of the %te magic
    from lamb.meta import te
    line = remove_comments(line)
    glob, line = magic_opt("lexicon", line)
    if not glob:
        glob, line = magic_opt("lex", line)
    if glob:
        use_env = True
    reduce, line = magic_opt("reduce", line)
    simplify, line = magic_opt("simplify", line)
    if line and line[-1] == ";":
        line = line[:-1]

    if env is None or not use_env:
        env = dict()
    var_env = vars_only(env)
    final_r = None
    with error_manager("Parsing of typed expression failed with exception:"):
        result = te(line, assignment=var_env)
        if is_te(result):
            result = result.regularize_type_env(var_env, constants=True)
            if glob:
                result = under_assignment(result, var_env)
            # TODO: should calling simplify_all simply entail reduce_all in the
            # first place?
            if reduce or simplify:
                result = result.reduce_all()
            if simplify:
                result = result.simplify_all()
        else:
            pass # warning here?
        # error before here leads to final_r == None
        final_r = result

    accum = dict()
    if final_r is not None:
        accum["_llast"] = final_r
    return (final_r, accum)


# used both in %(%)lamb and in %te
def under_assignment(right_side, env):
    assigned = right_side.under_assignment(env, compact=True)
    if assigned != right_side:
        from lamb.meta.ply import derived
        # subsitution via assignment may create derivational steps for
        # the type inference that aren't compatible with the derivation
        # we are trying to build; clobber them
        assigned.derivation = None
        assigned = derived(assigned, right_side, "Variable substitution from context")
    return assigned


def parse_right(left_s, right_s, env, constants=False):
    from lamb.meta import te
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


# overmatches relative to valid term names
term_re = r'_?[a-zA-Z0-9]+'
op_re = r'[!@%^&*~<>|\\/\-=+]+'
term_or_op_re = fr'({term_re}|{op_re})'


def build_assign_parser():
    eq_parser = (Whitespace()
                 + REParselet(r'=(?:<([a-zA-Z0-9_]*)>)?',
                      ast_label='transform',
                      error="Missing `=` in assignment")
                 + Whitespace())

    op_assign_parser = (Label('op_assign')
         + Precondition(Keyword('operator', error="Missing `operator` prefix"))
         + Whitespace()
         + REParselet(term_or_op_re, ast_label='operator')
         + Whitespace()
         + REParselet(r'(?:\((\d+)\))?', ast_label='arity')
         + eq_parser
         + REParselet(r'.*', ast_label='remainder'))

    lex_assign_parser = (
        Label("lex_assign")
        + Precondition(REParselet(r'\|\|', error="Missing interpretation brackets"))
        + REParselet(r'[a-zA-Z _]+[a-zA-Z0-9 _]*', ast_label='name')
        + REParselet(r'(?:\[(-?[0-9]+|\*)\])?\|\|', ast_label='index', error='error in lexical entry name')
        + eq_parser
        + REParselet(r'.*', ast_label='remainder'))

    from lamb.meta.parser import term_parser
    var_assign_parser = (
        Label("var_assign")
        + term_parser
        + eq_parser
        + REParselet(r'.*', ast_label='remainder'))

    assign_parser = Label('assignment', op_assign_parser
                                        | lex_assign_parser
                                        | var_assign_parser)
    return assign_parser


assign_parser = None


def insert_item(item, index, env):
    from lamb.lang import Items
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
    global assign_parser
    if assign_parser is None:
        # avoid circular import issues
        assign_parser = build_assign_parser()

    from lamb.meta.parser import TermNode, valid_op_symbol

    if env is None:
        env = {}
    var_env = vars_only(env)
    with error_manager():
        ast, _ = assign_parser.parse(s, i=i)
        # collect left_s name first for error messaging
        match ast:
            case ASTNode("assignment", [ASTNode("var_assign")]):
                left_desc = ast[0].term.name
            case ASTNode("assignment", [ASTNode("lex_assign")]):
                from lamb.lang import get_system
                left_desc = f"||{ast[0].name}||"
                a_ctl = get_system().assign_controller
                default = a_ctl.default()
                var_env = default.new_child(var_env)
            case ASTNode("assignment", [ASTNode("op_assign")]):
                left_desc = f"operator {ast[0].operator}"
            case ASTNode("assignment"):
                raise ParseError(f"Unknown assignment type `{ast.values}`", s=s, i=i)
            case _:
                raise ParseError(f"Unknown statement type `{ast.label}`", s=s, i=i)

        with parse_error_wrap(f"Assignment to `{left_desc}` failed"):
            match ast[0]:
                case ASTNode(transform=t, remainder=x):
                    right_side = parse_right(left_desc, x, var_env, constants=True)
                    if right_side is None:
                        return ({}, env)
                    right_side = apply_rs_transform(right_side, t, transforms=transforms)
                case _:
                    # should be unreachable, `remainder` matches ''.
                    return ({}, env)

            match ast[0]:
                case ASTNode("var_assign", term=TermNode(type=left_type) as t):
                    # if left_type is specified it, unify with right_side's
                    # type, and use that for the resulting term
                    if left_type is None:
                        left_type = right_side.type
                    if left_type != right_side.type:
                        right_side = right_side.ensure_typed_expr(right_side, typ=left_type)
                    term = t.instantiate(typ=right_side.type)
                    # NOTE side-effect here
                    env[term.op] = right_side
                    return ({term.op : right_side}, env)

                case ASTNode("lex_assign", name=name, index=index_str) as n:
                    from lamb.lang import Item
                    lex_name = name.replace(" ", "_")
                    if lex_name != name:
                        logger().info(f"Exporting item `||{name}||` to python variable `{lex_name}`.")
                    item = Item(lex_name, right_side)
                    if not index_str or index_str == "*":
                        if (lex_name in env and (ambiguity or index_str == "*")):
                            index = True
                        else:
                            index = None # replace existing item or add a new one
                    else:
                        index = int(index_str)
                    try:
                        insert_item(item, index, env)
                    except IndexError:
                        index_ast = n.map['index']
                        raise ParseError(f"Invalid index `{index}` in assignment to lexical entry `{left_desc}`", s=index_ast.s, i=index_ast.i)
                    return {lex_name: env[lex_name]}, env
                case ASTNode("op_assign", operator=op_symbol, arity=op_arity) as n:
                    from lamb.meta.core import op_from_te, registry
                    if not valid_op_symbol(op_symbol):
                        err_ast = n.map['operator']
                        raise ParseError(f"Invalid operator symbol `{op_symbol}`", s=err_ast.s, i=err_ast.i)
                    if op_arity:
                        op_arity = int(op_arity)

                    left_desc = f"operator {ast[0].operator}"
                    op_cls = op_from_te(op_symbol, right_side, arity=op_arity)
                    registry.add_operator(op_cls)
                    op = registry.get_operators(cls=op_cls)[0]
                    try:
                        # operators aren't stored in the env, so attempt to display them
                        # now (TODO: sequencing will be wrong)
                        from IPython.display import display
                        display(op)
                    except ImportError:
                        pass
                
                    # XX maybe store new operators as global state somehow, for easier access?
                    return ({}, env)
    return ({}, env)


def remove_comments(s):
    """remove comments (prefaced by #) from a single line"""
    r = s.split("#")
    return r[0].rstrip()


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


def fullvar(d, s):
    from lamb.meta import TypedTerm
    if isinstance(s, TypedTerm):
        return s
    else:
        return TypedTerm(s, d[s].type)


def html_output(accum):
    # legacy function, maybe remove at some point
    x = utils.Namespace(accum)
    return utils.show(markdown=x._repr_markdown_(), plain=repr(x))


def parse_qtree(s, i=0):
    s = s.strip()
    r, i = parse_qtree_r(s, i)
    return r

def consume_curly_bracketed(s, i):
    """Parse a balanced expression with curly braces.  Accept any character
    inside the curly braces."""
    # TODO: implement escaped curly braces?
    i = consume_char(s, i, "{", "Missing opening '{'")
    accum = ""
    balance = 1
    start_i = i
    while i < len(s):
        if s[i] == "{":
            balance += 1
            i += 1
        elif s[i] == "}":
            balance -= 1
            i += 1
            if balance == 0:
                break
        else:
            accum += s[i]
            i += 1
    if balance != 0:
        raise ParseError("Unbalanced '{...}' expression", s, i)
    return (accum, i)

def consume_qtree_node(s, i):
    if s[i] == "{":
        (label, i) = consume_curly_bracketed(s, i)
        return (label, i)
    else:
        (m_group, new_i) = consume_pattern(s, i, r'\.([a-zA-Z0-9\(\)\:\-]*)\s')
        if m_group is None:
            return (None, None)
        return (m_group, new_i)

def parse_qtree_child(s, i):
    i = consume_whitespace(s, i)
    # this is a bit hacky, maybe want to generalize to strings that may involve
    # curly braces
    if s[i] == "{":
        return consume_curly_bracketed(s, i)
    elif s[i] == "[":
        return parse_qtree_r(s, i)
    else: # should be just a string
        m_group, new_i = consume_pattern(s, i, r'([a-zA-Z0-9\(\)\:\-]*)')
        if m_group is None or len(m_group) == 0:
            # redundant given the current regex but keeping it in case I want
            # to change that
            return (None, i)
        else:
            return m_group, new_i

def parse_qtree_r(s, i=0):
    """Parse a bracketed qtree structure."""
    i = consume_char(s, i, "[", "Missing '['")
    (m_group, new_i) = consume_qtree_node(s, i)
    if m_group is None or len(m_group) == 0:
        label = ""
    else:
        label = m_group
        i = new_i
    children = []
    i = consume_whitespace(s, i)
    # seems a bit brittle?
    while i < len(s) and s[i] != "]":
        child, i = parse_qtree_child(s, i)
        if child is None: # no child description found
            break
        children.append(child)
        i = consume_whitespace(s, i)
    if len(children) == 0:
        children.append("")
    i = consume_whitespace(s, i)
    i = consume_char(s, i, "]", "Missing ']'")
    return (Tree(label, children=children), i)


def flatten_paren_struc(struc):
    """Flatten a parsed structure back into a string; mainly used for errors"""
    s = ""
    for sub in struc:
        if isinstance(sub, str):
            s += sub
        else:
            s += flatten_paren_struc(sub)
    return s.strip()

global all_brackets, close_brackets
all_brackets = {"(" : ")", "{" : "}"}
close_brackets = {all_brackets[y] : y for y in all_brackets.keys()}


def bracketed(struc, brackets=None):
    if brackets is None:
        brackets = all_brackets
    if (len(struc) > 0
            and isinstance(struc[0], str)
            and struc[0] in brackets
            and all_brackets[struc[0]] == struc[-1]):
        return struc[0]
    else:
        return None


def debracket(struc):
    # n.b. this does nothing on cases like [['(', 'stuff', ')']]
    if bracketed(struc):
        return debracket(struc[1:-1])
    else:
        return struc


def struc_split(struc, sep):
    # XX implement maxsplit, this currently does exactly 1 split
    for i in range(len(struc)):
        if isinstance(struc[i], str) and (pos := struc[i].find(sep)) >= 0:
            l = struc[0:i]
            r = struc[i+1:]
            if pos > 0:
                l = l + [struc[i][:pos]]
            if pos + len(sep) < len(struc[i]):
                r = [struc[i][pos+len(sep):]] + r
            return l, r
    return (struc,)


def unconsumed(struc):
    if isinstance(struc, str):
        i = consume_whitespace(struc, 0)
        return i < len(struc)
    else:
        for s in struc:
            if unconsumed(s):
                return True
    return False


def struc_dirstrip(struc, left=True):
    # this guarantees at least len 1 on the return
    if not struc:
        return [""]

    if left:
        target = 0
        remainder = slice(1, None)
        f = lambda s: s.lstrip()
        combine = lambda s,struc: [s] + struc
    else:
        target = -1
        remainder = slice(None, -1)
        f = lambda s: s.rstrip()
        combine = lambda s,struc: struc + [s]

    # no recursing
    if not isinstance(struc[target], str):
        return struc
    stripped = f(struc[target])

    if len(stripped) == 0:
        return struc_dirstrip(struc[remainder], left=left)
    else:
        return combine(stripped, struc[remainder])


def struc_lstrip(struc):
    return struc_dirstrip(struc, left=True)


def struc_rstrip(struc):
    return struc_dirstrip(struc, left=False)


def struc_strip(struc):
    return struc_lstrip(struc_rstrip(struc))


def parse_paren_str_r(s, i, stack, initial_accum=None, type_sys=None):
    from lamb.meta.parser import term_symbols_re
    # XX type_sys param vs parsing_ts()
    accum = ""
    seq = list()
    if initial_accum is not None:
        seq.append(initial_accum)
    start_i = i
    while i < len(s):
        # TODO: code dup/overlap with parse_term
        if (i > 0 and s[i] == "_" and s[i-1] == "_"):
            # without special handling here for this error case, an error
            # message can be triggered on eval and is extremely cryptic.
            raise ParseError("Stray `_` in expression", s=s, i=i)
        elif (i > 0 and s[i] == "_" and re.match(term_symbols_re, s[i-1])
                        and type_sys != None):
            accum += "_"
            # have to parse type here in order to handle bracketing in types
            # correctly. I don't think there's a shortcut to this.  In the long
            # run, this should do proper tokenizing of terms.
            typ, end = type_sys.type_parser_recursive(s, i+1)
            assert(typ is not None)
            # this is unfortunate...
            accum += s[i+1:end]
            i = end
        elif s[i] in all_brackets:
            stack.append(s[i])
            i += 1

            r, new_i = parse_paren_str_r(s, i, stack, initial_accum=stack[-1],
                                                            type_sys=type_sys)
            if len(accum) > 0:
                seq.append(accum)
                accum = ""
            seq.append(r)
            i = new_i
        elif s[i] in close_brackets:
            if len(stack) > 0 and s[i] == all_brackets[stack[-1]]:
                if len(accum) > 0:
                    seq.append(accum)
                    accum = ""
                stack.pop()
                seq.append(s[i])
                i += 1
                return (seq, i)
            else:
                raise ParseError("Unbalanced `%s...%s` expression"
                                        % (close_brackets[s[i]], s[i]), s, i)
        else:
            accum += s[i]
            i += 1
    if len(accum) > 0:
        seq.append(accum)
    return (seq, i)


def parse_paren_str(s, i, type_sys=None):
    """Turn a string with parenthesis into a structured representation,
    checking balance.

    The structure consists of a list of strings/lists.  Sub-elements that are
    lists have the same structure. Each distinct sub-element represents a
    parenthesized grouping.

    Right now only pays attention to () and {}."""
    stack = list()
    (seq, i) = parse_paren_str_r(s, i, stack, type_sys=type_sys)
    if len(stack) != 0:
        raise ParseError("Unbalanced '%s...%s' expression at end of string" %
                                    (stack[-1], all_brackets[stack[-1]]), s, i)
    return (seq, i)
