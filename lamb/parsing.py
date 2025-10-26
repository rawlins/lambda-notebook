import sys, re, traceback, collections, enum, typing, dataclasses
from contextlib import contextmanager
from dataclasses import dataclass, field, fields

from typing import Optional

# imported by meta
from lamb import utils
from lamb.utils import * # TODO: remove
from lamb.display import assignment_repr

try:
    EnumClass = enum.StrEnum
except:
    EnumClass = enum.Enum

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
        self.has_preconditions = None
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
        if self.met_preconditions:
            pre = ""
        else:
            pre = " (precondition)"
        if classname:
            m = f"{self.__class__.__name__}: {self.msg}{pre}"
        else:
            m = f"{self.msg}{pre}"
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


@dataclass
class ASTNode:
    label: Optional[str | type] = field(default=None, kw_only=True)
    children: list[object] = field(default_factory=list, kw_only=True) # should be list[ASTNode], but that fails to parse
    s: Optional[str] = field(default=None, kw_only=True)
    i: Optional[int] = field(default=None, kw_only=True)
    __match_args__ = ("label", "children")

    _no_parse = {'label', 'children', 's', 'i'}

    def __post_init__(self):
        if (l := getattr(self, 'class_label', None)):
            self.label = l
        self.map = {v.label: v for v in self.children if isinstance(v, ASTNode) and v.label is not None}
        self._sub_fields = tuple(f for f in fields(self) if f.name not in self._no_parse)

    def finalize(self):
        if isinstance(self.label, type):
            return self.label.from_ast(self)
        else:
            return self

    def label_name(self):
        if self.label is None:
            return "anonymous parse unit"
        else:
            return f"`self.label`"

    def get(self, x, default=None, error=None, force_raw=False):
        if x in self.map:
            r = self.map[x]
            if isinstance(r, ASTNode) and r.__class__ != ASTNode:
                # proper subclass: assume it is already parsed.
                return r
            elif (not force_raw and isinstance(r, ASTNode)
                    and len(r.children) == 1
                    and not isinstance(r.children[0], ASTNode)):
                # unparsed non-branching node with a value: return that value
                return r.children[0]
            elif not force_raw and isinstance(r, ASTNode) and len(r.children) == 0:
                # no children at all: return None
                # XX is this correct?
                return None
            else:
                return r

        if error:
            if error is True:
                error = f"Missing field `{x}` in {self.label_name()}"
            raise ParseError(error, s=self.s, i=self.i)
        else:
            return default


    def left_extend(self, node):
        # assumption: `node` comes from a substring that is linearly to the left
        # of self, and we should use node's s/i values
        return ASTNode(label=self.label, children=(node.children + self.children), s=node.s, i=node.i)

    def right_extend(self, node):
        return ASTNode(label=self.label, children=(self.children + node.children), s=self.s, i=self.i)

    def left_attach(self, node):
        # assumption: `node` comes from a substring that is linearly to the left
        # of self, and we should use node's s/i values
        if node.label is None:
            return self.left_extend(node)
        else:
            return ASTNode(label=self.label, children=([node] + self.children), s=node.s, i=node.i)

    def right_attach(self, node):
        if node.label is None:
            return self.right_extend(node)
        else:
            return ASTNode(label=self.label, children=(self.children + [node]), s=node.s, i=node.i)

    def __contains__(self, x):
        return x in self.map

    def __len__(self):
        return len(self.children)

    def __bool__(self):
        # override default behavior based on length
        return True

    def __getitem__(self, i):
        return self.children[i]

    def _to_field_map(self):
        return {f.name: getattr(self, f.name) for f in self._sub_fields}

    def __repr__(self):
        if not self.children:
            # if `children` is empty, try printing the fields, to handle subclasses
            # that don't use `children`
            return f"({self.label}: {repr(self._to_field_map())})"
            # return f"({self.label}: {repr(self.map)})"
        else:
            return f"({self.label}: {', '.join(repr(v) for v in self.children)})"

    def to_tree(self):
        def _as_tree(x, label=None):
            if isinstance(x, ASTNode):
                # assume that `x` provides the label also
                return x.to_tree()
            elif label is not None:
                return Tree(label, [repr(x)])
            else:
                return repr(x) # leaf node

        m = self._to_field_map()
        children = [_as_tree(m[k], label=k) for k in m]
        children = children + [_as_tree(v) for v in self.children]
        if isinstance(self.label, str):
            label = self.label
        elif isinstance(self.label, type):
            label = self.label.__name__
        else:
            label = repr(self.label)
        return Tree(label, children)

    def instantiate(self, **kwargs):
        if len(self.children) == 1 and isinstance(self.children[0], ASTNode):
            return self.children[0].instantiate(**kwargs)

        # if this shows up, it's a parser bug
        raise NotImplementedError(f"Don't know how to instantiate generic ASTNode: {repr(self)}")

    @classmethod
    def map_from_ast(cls, a, allow_remainder=False, s=None, i=None):
        if a is None:
            return cls(s=s, i=i) # may error

        # currently these params are unused except for the None case, but
        # do this to be robust
        if s is None:
            s = a.s
        if i is None:
            i = a.i
        def a_get(f):
            # use defaults as a proxy for Optional
            if f.default is not dataclasses.MISSING:
                return a.get(f.name, default=f.default)
            elif f.default_factory is not dataclasses.MISSING:
                return a.get(f.name, default=f.default_factory())
            else:
                return a.get(f.name, error=True)
        # if a node has multiple children with a label in `fields`, this will
        # consume only the first. Probably not what you want!
        m = {f.name: a_get(f) for f in fields(cls) if f.name not in cls._no_parse}
        if len(m) < len(a.children):
            if allow_remainder:
                # consume the remainder into `children`
                return cls.seq_from_ast(a, ast_constraint=None, **m)
            else:
                missing = [c.label for c in a.children if c.label not in fields]
                # XX error is confusing for unlabeled / repeated children
                raise ParseError(f"Internal parser error: parsing to `{cls}` failed to consume fields: `{', '.join(missing)}`", s=s, i=i)
        return cls(s=s, i=i, **m)

    @classmethod
    def seq_from_ast(cls, a, ast_constraint=None, s=None, i=None, **fields):
        if a is None:
            return cls(s=s, i=i, **fields)
        if s is None:
            s = a.s
        if i is None:
            i = a.i
        children = [c for c in a.children if c.label not in fields]
        if len(children) + len(fields) < len(a.children):
            # something is designed wrong. For example, this would be triggered
            # by trying to parse an chained op expression to a class with a
            # field name `op`, because map parsing would consume only the first
            # instance of `op`.
            raise ParseError(f"Internal parser error: `{cls}` has a field name for a repeated AST child label", s=s, i=i)
        if ast_constraint:
            for x in children:
                if not isinstance(x, ast_constraint):
                    if isinstance(x, ASTNode):
                        s = x.s
                        i = x.i
                    raise ParseError(f"Failed to match `{ast_constraint.class_label}` in `{a.label}`",
                        s=s, i=i)
        return cls(children=children, s=s, i=i, **fields)

    @classmethod
    def from_ast(cls, a, s=None, i=None):
        # default is the most flexible parsing option: any fields in a subclass
        # are parsed, and the remainder is inserted into `children`.
        return cls.map_from_ast(a, allow_remainder=True, s=s, i=i)


# convenience decorator for ASTNode subclasses
def astclass(label, *, repr=False, **kwargs):
    """Convenience decorator for ASTNode subclasses. Sets the class's label,
    enforces `@dataclass`, and defaults `repr` to False (so that the ASTNode
    repr is inherited rather than overridden by dataclass)."""
    def inner(_cls):
        r = dataclass(_cls, repr=repr, **kwargs)
        r.class_label = label
        return r
    return inner


# a parse state is a tuple (n, i) where `n` is None or an ASTNode instance, and
# `i` is the current position in the string being parsed


def seq_result(parser, accum, cur, s, i):
    label_single = getattr(parser, 'label_single', False)
    force_node = getattr(parser, 'force_node', False)
    if label_single is not False and len(accum) <= 1:
        label = label_single
    else:
        label = parser.ast_label
    if not force_node and not accum:
        # interpret this as a succesful consumer-only parse
        return None, cur
    elif not force_node and not label and len(accum) == 1 and isinstance(accum[0], ASTNode):
        # don't add extra AST nodes for unlabeled sequences unless forced
        return accum[0], cur
    else:
        return ASTNode(label=label, children=accum, s=s, i=i), cur


def seq_extend(accum, n):
    if n:
        if n.label is None:
            # This will wipe out an unlabeled node with no values
            accum.extend(n.children)
        else:
            accum.append(n)


class Parselet(object):
    parser = None
    def __init__(self, parser, ast_label=None, error=None, skip_trivial=False):
        if parser is not None:
            # only override class-level field if something non-trivial is
            # provided. This is primarily to support the subclassing behavior
            # of `Unit`.
            self.parser = parser
        self.ast_label = ast_label
        self.error_msg = error
        self.skip_trivial = skip_trivial

    def copy_args(self):
        return dict(ast_label=self.ast_label, error=self.error_msg, skip_trivial=self.skip_trivial)

    def rule_name(self):
        if self.ast_label is None:
            return "anonymous rule"
        else:
            return f"rule `{self.ast_label}`"

    def default_error(self, s, i):
        return f"Failed to parse {self.rule_name()}"

    def error(self, s, i, error=None, met_preconditions=True):
        if error:
            e = error
        elif self.error_msg:
            e = self.error_msg
        else:
            e = self.default_error(s, i)
        raise ParseError(e, s=s, i=i, met_preconditions=met_preconditions)

    def parse(self, s, i=0):
        # this code is more general than subclasses, because it allows for
        # wrapping a parsing function
        if self.parser is None:
            # noop succesful parse
            return None, i
        result = self.parser(s, i)
        if not isinstance(result, collections.abc.Sequence):
            result = (result,)
        if result[-1] is None:
            # parser returned None, or returned None for position
            # interpret this case as a failed parse
            self.error(s, i)
        new_i = result[-1]
        result = [x for x in result[0:-1] if x is not None]
        if not result:
            # parser just returned a position
            # interpret this case as a consumer-only parse
            return None, new_i
        if self.skip_trivial and len(result) == 1 and isinstance(result[0], ASTNode):
            return result[0], new_i
        return ASTNode(label=self.ast_label, children=result, s=s, i=i), new_i

    def __call__(self, s, i=0):
        return self.parse(s, i=i)

    def __or__(self, other):
        return Disjunctive(self, other)

    def __add__(self, other):
        return Sequence(self, other)

    def __matmul__(self, other):
        return LateDisjunctive(self, other)


class Unit(Parselet):
    def __init__(self, parser=None):
        if parser is not None and self.parser_builder:
            raise ParseError("Internal parser error: `Unit` parser builder subclass has doubly-supplied parser on construction")
        elif self.parser is not None:
            if parser is not None:
                # subclasses will typically not bother with __init__, so validate
                # this case manually
                raise ParseError("Internal parser error: doubly-supplied parser for `Unit` subclass")
            # leave parser defined as a class attribute, by passing None to
            # superclass
        super().__init__(parser)

    @classmethod
    @property
    def parser_builder(cls):
        return bool(getattr(cls, 'build_parser', False))

    @classmethod
    def memoize_parser(cls):
        # memoize the parser as a class-level attribute
        cls.parser = cls.build_parser()

    def get_parser(self):
        if self.parser is None and self.parser_builder:
            # if a subclass defines `build_parser`, call it and memoize the
            # resulting parser at this point. This allows a parser to be
            # instantiated at the module level without worrying about circular
            # import issues.
            self.memoize_parser()
        if self.parser is None:
            raise ParseError("Internal parser error: Unit is missing parser", s=s, i=i)
        return self.parser

    def parse(self, s, i=0):
        n, i = self.get_parser().parse(s, i)
        if n is not None:
            n = n.finalize()
        return n, i


class Label(Parselet):
    """Dummy Parselet that serves only to provide an AST label"""
    def __init__(self, ast_label, parser=None, force_node=True, defer=False):
        self.force_node = force_node
        self.defer = defer
        if not self.defer and isinstance(ast_label, type) and issubclass(ast_label, ASTNode):
            self.label_class = ast_label
            ast_label = self.label_class.class_label
        else:
            self.label_class = None
        super().__init__(parser, ast_label=ast_label)

    def parse(self, s, i=0):
        if self.parser is not None:
            n, new_i = self.parser.parse(s, i)
        else:
            n, new_i = super().parse(s, i=i)

        if not n:
            if self.force_node:
                if self.label_class:
                    # `from_ast` will need to handle this case. By default:
                    # call label_class's constructor with no arguments.
                    return self.label_class.from_ast(None, s=s, i=i), new_i
                else:
                    return ASTNode(label=self.ast_label, s=s, i=i), new_i
            else:
                # consumer-only parse
                return None, new_i
        else:
            if n.label is None:
                # relabel an existing None-labeled node
                if self.label_class:
                    n = self.label_class.from_ast(n)
                else:
                    # relabel as a side effect
                    n.label = self.ast_label
                return n, new_i
            else:
                # `n` is already labeled, add a new parent
                n = ASTNode(label=self.ast_label, children=[n], s=s, i=i)
                if self.label_class:
                    n = self.label_class.from_ast(n)
                return n, new_i

    def __add__(self, other):
        if self.label_class:
            l = self.label_class
        else:
            l = self.ast_label
        if self.parser is not None:
            # Note: some potentially counterintuitive behavior if self.parser
            # is also a Label.
            return Label(l, parser=self.parser + other, force_node=self.force_node, defer=self.defer)
        else:
            return Label(l, parser=Sequence(other), force_node=self.force_node, defer=self.defer)


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
                return None, i


class REParselet(Parselet):
    def __init__(self, regex, consume=None, ast_label=None, flags=0, **kwargs):
        self.raw_regex = regex
        regex = re.compile(regex, flags=flags)
        # by default: consume if there is no label and no capturing groups
        if consume is None:
            consume = not bool(ast_label) and not regex.groups
        self.consume = consume
        super().__init__(regex, ast_label=ast_label, **kwargs)

    def default_error(self, s, i):
        return f"Failed to match pattern for {self.rule_name()} `{self.raw_regex}`"

    def parse(self, s, i=0):
        m = self.parser.match(s, i)
        if m:
            new_i = m.end()
            if self.consume:
                # preempt any groups
                return None, new_i
            # could do something with named groups
            result = m.groups()
            # set the `i` value based on the group beginning, not the whole
            # match. (XX generalize to multiple groups)
            ret_i = 0
            if result and (test_i := m.start(1)) >= 0:
                ret_i = test_i
            elif not result:
                # use entire match
                result = (m.group(),)
            # XX should this use seq_result?
            return ASTNode(label=self.ast_label, children=result, s=s, i=ret_i), new_i
        else:
            self.error(s, i)


class Keyword(REParselet):
    def __init__(self, kw, **kwargs):
        # `kw` is intended to be alphanumeric here
        # end token check: only match if we do not continue matching alphanum
        # characters next (XX op version of this?)
        regex = rf'{kw}(?![\w])'
        super().__init__(regex, **kwargs)


class Token(REParselet):
    def __init__(self, re, alphanum=False, **kwargs):
        if alphanum:
            regex = rf'\s*{re}(?![\w])\s*'
        else:
            regex = rf'\s*{re}\s*'
        super().__init__(regex, **kwargs)


# XX linebreaks
def Whitespace(plus=False):
    if plus:
        return REParselet(r'\s+', consume=True, error="failed to match whitespace")
    else:
        return REParselet(r'\s*', consume=True)


class Sequence(Parselet):
    def __init__(self, *parsers, force_node=True, **kwargs):
        self.force_node = force_node
        super().__init__(list(parsers), **kwargs)

    def parse(self, s, i=0):
        accum = []
        cur = i
        for p in self.parser:
            n, cur = p.parse(s, cur)
            seq_extend(accum, n)

        return seq_result(self, accum, cur, s, i)

    def copy(self):
        return Sequence(*self.parser, **self.copy_args())

    def __add__(self, other):
        r = self.copy()
        r.parser.append(other) # left association
        return r


class Precondition(Sequence):
    def __init__(self, pre, main=None, ast_label=None, **kwargs):
        # ast_label is unused in parsing
        self.pre = pre
        if main is None:
            main = []
        super().__init__(*main, ast_label=ast_label, **kwargs)

    def parse(self, s, i=0):
        accum = []
        try:
            n, cur = self.pre.parse(s, i)
            seq_extend(accum, n)
        except ParseError as e:
            e.has_preconditions = True
            e.met_preconditions = False
            raise e

        try:
            # XX code dup with superclass
            for p in self.parser:
                n, cur = p.parse(s, cur)
                seq_extend(accum, n)
        except ParseError as e:
            e.has_preconditions = True
            raise e

        return seq_result(self, accum, cur, s, i)

    def copy(self):
        return Precondition(self.pre, main=self.parser, **self.copy_args())



class Repeat(Parselet):
    def __init__(self, parser, allow_empty=True, force_node=True, check_pre=False, **kwargs):
        self.allow_empty = allow_empty
        self.force_node = force_node
        self.check_pre = check_pre
        super().__init__(parser, **kwargs)

    def parse(self, s, i=0):
        accum = []
        cur = i
        found_any = False
        while cur < len(s):
            try:
                n, cur = self.parser.parse(s, cur)
                found_any = True
                seq_extend(accum, n)
            except ParseError as e:
                if self.check_pre and e.met_preconditions:
                    raise e
                break
        if not self.allow_empty and not found_any:
            raise ParseError(f"Failed to match any instances of `{self.ast_label}`", s=s, i=i)
        return seq_result(self, accum, cur, s, i)


class Join(Parselet):
    # basically equivalent to elem + Repeat(join + elem), but it produces a
    # flat ast (and has some more bells and whistles)
    def __init__(self, join, elem,
                allow_empty=True, allow_final=False, initial_join=False,
                label_single=False, force_node=True, **kwargs):
        self.join = join
        self.elem = elem
        self.allow_empty = allow_empty
        self.allow_final = allow_final
        self.initial_join = initial_join
        self.label_single = label_single
        self.force_node = force_node
        super().__init__([join, elem], **kwargs)

    def parse(self, s, i=0):
        accum = []
        cur = i
        found_any = False
        join_last = False
        if self.initial_join:
            # if this is set, we are expecting the string to *start* with the
            # join.
            try:
                n, cur = self.join.parse(s, cur)
                seq_extend(accum, n)
                join_last = True
            except ParseError as e:
                if not self.allow_empty:
                    raise e
                else:
                    # nothing parsed, treat it as an allowed empty sequence
                    return seq_result(self, accum, cur, s, i)

        while cur < len(s):
            try:
                n, cur = self.elem.parse(s, cur)
                seq_extend(accum, n)
                found_any = True
                join_last = False

                n, cur = self.join.parse(s, cur)
                seq_extend(accum, n)
                join_last = True

            except ParseError as e:
                if not found_any and not self.allow_empty:
                    raise e
                if join_last and e.has_preconditions and e.met_preconditions:
                    # we failed while already committed to elem
                    # XX is this too aggressive?
                    raise e
                break
        if not found_any and not self.allow_empty:
            raise ParseError(f"Failed to match any instances of `{self.ast_label}`", s=s, i=i)
        if join_last and not self.allow_final:
            if self.join.ast_label is not None:
                join_name = f"`{self.join.ast_label}`"
            else:
                join_name = "join"
            raise ParseError(f"Parsing sequence `{self.ast_label}` ended in invalid final {join_name}", s=s, i=i)
        return seq_result(self, accum, cur, s, i)


class Disjunctive(Parselet):
    def __init__(self, *parsers, **kwargs):
        super().__init__(list(parsers), **kwargs)

    def default_error(self, s, i):
        return f"Failed to find disjunct for {self.rule_name()}"

    def copy(self):
        return Disjunctive(*self.parser, **self.copy_args())

    def parse(self, s, i=0):
        for p in self.parser:
            with try_parse():
                n, new_i = p.parse(s, i)
                if not n:
                    # interpret this as a succesful consumer-only parse
                    return None, new_i
                # only label if either we don't have an ASTNode, or this parser
                # explicitly provides a label.
                if self.ast_label is None:
                    return n, new_i
                else:
                    return ASTNode(label=self.ast_label, children=[n], s=s, i=i), new_i
        # if we get to here, all parsers raised with met_preconditions=False.
        # send that same flag upwards in case this is part of another
        # Disjunctive
        self.error(s, i, met_preconditions=False)

    def __or__(self, other):
        r = self.copy()
        r.parser.append(other) # left association
        return r


class LateDisjunctive(Parselet):
    # Disjunctive rules with shared prefix, where disambiguation comes late. I.e.
    # S -> prefix parser_1
    # S -> prefix parser_2
    # ...
    # S -> prefix parser_n
    # as usual, parsers must disambiguate and handle preconditions. The prefix
    # is automatically treated as a precondition.
    def __init__(self, prefix, *parsers, **kwargs):
        # wrapping this in a Precondition is a bit heavy-handed, but it is
        # guaranteed to do what we want
        if not isinstance(prefix, Precondition):
            prefix = Precondition(prefix)
        self.prefix = prefix
        # n.b. prefix is not stored in `self.parser`
        super().__init__(list(parsers), **kwargs)

    def default_error(self, s, i):
        return f"Failed to find late disjunct for {self.rule_name()}"

    def copy(self):
        return LateDisjunctive(self.prefix, *self.parser, **self.copy_args())

    def parse(self, s, i=0):
        try:
            prefix_n, new_i = self.prefix.parse(s, i=i)
        except ParseError as e:
            # errors from within prefix can be arbitrarily unrelated, so
            # repackage...
            raise ParseError(f"Failed to match prefix for {self.rule_name()}",
                e=e, s=s, i=i, met_preconditions=e.met_preconditions)
        for p in self.parser:
            with try_parse():
                disj_n, new_i = p.parse(s, i=new_i)

                if prefix_n and disj_n:
                    # insert the prefix AST node under the disjunction result
                    # if prefix_n has no label, this will merge sequences
                    result = disj_n.left_attach(prefix_n)
                elif disj_n:
                    # prefix was consumer-only
                    result = disj_n
                else:
                    # either disjunct or everything was consumer-only
                    result = prefix_n

                if not result:
                    # interpret this as a succesful consumer-only parse
                    return None, new_i
                # same labeling logic as Disjunctive at this point
                elif self.ast_label is None:
                    return result.finalize(), new_i
                else:
                    return ASTNode(label=self.ast_label, children=[result.finalize()], s=s, i=i), new_i
        # if we get to here, all parsers raised with met_preconditions=False.
        # send that same flag upwards in case this is part of another
        # Disjunctive
        # n.b. an empty self.parser errors...
        self.error(s, i, met_preconditions=False)

    def __matmul__(self, other):
        r = self.copy()
        r.parser.append(other)
        return r


class LeftRecursive(Parselet):
    # parse a left-recursive rule of the form:
    # S -> S + parsers[0]
    # S -> S + parsers[1]
    # ...
    # S -> S + parsers[n]
    # S -> prefix
    def __init__(self, prefix, *parsers, force_node=True, **kwargs):
        parsers = list(parsers)
        # # ensure that the final disjunct is a dummy parser so that we can
        # # gracefully fall back to the terminal-only case
        self.prefix = prefix
        self.force_node = force_node
        parser = Repeat(Disjunctive(*parsers), check_pre=True)
        super().__init__(parser, **kwargs)

    def ast_group_left(self, a):
        if len(a) <= 1:
            return a
        ast = a[0]
        for i in range(1, len(a)):
            ast = ASTNode(label=a[i].label, children=[ast] + a[i].children, s=a[i].s, i=a[i].i).finalize()
        return [ast]


    def parse(self, s, i=0):
        cur = i
        accum = []
        prefix_n, cur = self.prefix.parse(s, i=cur)
        seq_extend(accum, prefix_n)
        n, cur = self.parser.parse(s, i=cur)
        seq_extend(accum, n)
        if not accum:
            return None, cur
        else:
            return seq_result(self, self.ast_group_left(accum), cur, s, i)


def te_only(env):
    """Ensure that env is a 'pure' expression assignment -- exclude anything but
    TypedExprs."""
    return {key: env[key] for key in env if is_te(env[key])}


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
# note that recursive use of this with `errors_raise` will result in extra messaging
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
            if display:
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
    var_env = te_only(env)
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


class Statement(EnumClass):
    ASSIGNMENT = "assignment"
    VAR_ASSIGN = "var_assign"
    LEX_ASSIGN = "lex_assign"
    OP_ASSIGN = "op_assign"


class Attr(EnumClass):
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
        right_side = parse_right(self.left_desc(), self.expr, var_env, constants=True)
        if right_side is not None:
            right_side = apply_rs_transform(right_side, self.transform, transforms=transforms)
        return right_side


@astclass(Statement.VAR_ASSIGN)
class VarAssignAST(AssignmentAST):
    term: ASTNode # really, TermNode

    def left_desc(self):
        return self.term.name

    def instantiate(self, var_env, transforms):
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
        term = self.term.instantiate(typ=right_side.type)
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

    def instantiate(self, var_env, transforms):
        from lamb.lang import Item

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

    def instantiate(self, var_env, transforms):
        raise NotImplementedError()


class AssignmentParser(Unit):
    @classmethod
    def build_parser(cls):
        # build cls.parser on first instantiation, to avoid circular import
        # issues. After first instantiation, this is memoized.
        from lamb.meta.parser import term_parser

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
    from lamb.meta.parser import TermNode, valid_op_symbol

    if env is None:
        env = {}
    var_env = te_only(env)
    raw_ast, _ = assign_parser.parse(s, i=i)
    match raw_ast:
        case ASTNode(Statement.ASSIGNMENT, [VarAssignAST() | OpAssignAST()]):
            pass
        case ASTNode(Statement.ASSIGNMENT, [LexAssignAST()]):
            from lamb.lang import get_system
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
                term_name, right_side = ast.instantiate(var_env, transforms)
                if term_name is None:
                    return ({}, env)
                else:
                    # # NOTE side-effect here
                    env[term_name] = right_side
                    return ({term_name : right_side}, env)
            case LexAssignAST():
                item = ast.instantiate(var_env, transforms)
                if item is None:
                    return {}, env
                try:
                    insert_item(item, ast.get_index(env, ambiguity), env)
                except IndexError:
                    raise ParseError(f"Invalid index `{ast.index}` in assignment to lexical entry `{left_desc}`", s=ast.s, i=ast.i)
                return {item.name: env[item.name]}, env
            case OpAssignAST(op=op_symbol, arity=arity):
                from lamb.meta.core import op_from_te, registry

                right_side = ast.eval_right_side(var_env, transforms)
                if right_side is None:
                    return {}, env

                if not valid_op_symbol(op_symbol):
                    err_ast = raw_ast[0].map[Attr.OP]
                    raise ParseError(f"Invalid operator symbol `{op_symbol}`", s=err_ast.s, i=err_ast.i)
                if arity is not None:
                    arity = int(arity)
                op_cls = op_from_te(op_symbol, right_side, arity=arity)
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
            case _:
                raise ParseError(f"Unknown assignment type: {raw_ast}", s=raw_ast.s, i=raw_ast.i)
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
    # XX type_sys param vs get_type_system()
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
