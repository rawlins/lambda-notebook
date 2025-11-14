import sys, re, traceback, collections, enum, typing, dataclasses
from contextlib import contextmanager
from dataclasses import dataclass, field, fields

from typing import Optional

# imported by meta
from lamb import utils
from lamb.utils import * # TODO: remove
from lamb.display import assignment_repr

Tree = utils.get_tree_class()

# wrap some common circular import cases:
def logger():
    from lamb.meta import logger
    return logger

def is_te(x):
    from lamb.meta import is_te
    return is_te(x)

class ParseError(Exception):
    def __init__(self, msg, s=None, i=None, met_preconditions=True, e=None, has_preconditions=None):
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
        # set to False to indicate that a parser did not find
        # preconditions for what it is supposed to parse
        self.met_preconditions = met_preconditions
        self.has_preconditions = has_preconditions
        self.has_note = False

    def _try_add_note(self):
        if self.has_note or self.i is None:
            return
        try:
            # when showing the error output in a regular stack trace, use
            # the note mechanism to show the error string as a multilne
            # string
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
            # note: the \n here is because in some circumstances (unclear to
            # me), markdown formatting immediately followed by html code is
            # broken
            sep = plain and "\n" or "\n<br />&nbsp;&nbsp;&nbsp;&nbsp;"
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
            m = f"{m}{aux}"
            if allow_note and self.has_note:
                return m
            return utils.error_pos_str(self.s, self.i, prefix=m,
                                    plain=True, multiline=multiline)

    def __str__(self):
        # used in stack trace. Therefore, we don't print the classname, and
        # don't try multiline stuff directly, because the context isn't fully
        # predictable. However, in python 3.11+, use the `add_note` mechanism
        # to show multiline messaging. (Note that the note is not part of
        # the return value, but is added by side effect!)
        return self.tostring(classname=False, allow_note=True, multiline=False)

    def _repr_markdown_(self):
        # it's convenient to use markdown here for backticks, but colab will
        # strip out the color. So, use both red and bold.
        aux = self._aux_str(plain=False)
        # note: the case that combines an aux string and an error position is
        # relatively untested
        if self.s is None:
            m = f"{self.msg}{aux}"
        elif self.i is None:
            m = f"{self.msg}, in string `{self.s}`{aux}"
        else:
            m = utils.error_pos_str(self.s, self.i, prefix=f"{self.msg}{aux}",
                                    plain=False, multiline=True)
        # it's convenient to use markdown here for backticks, but colab will
        # strip out the color. So, use both red and bold.
        return f"<span style=\"color:red\">**{self.__class__.__name__}**</span>: {m}"

    def __repr__(self):
        return self.tostring(multiline=False)

    def _repr_pretty_(self, p, cycle):
        return p.text(self.tostring())


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


def consume_whitespace(s, i, plus=False, error=None):
    m_group, i = consume_pattern(s, i, r'\s*', error)
    return i


@dataclass
class ParseState:
    s: str
    i: typing.Optional[int] = 0
    e: typing.Optional[ParseError] = None

    def update(self, i):
        return dataclasses.replace(self, i=i)

    def error(self, m_or_e, pos=None, **kwargs):
        if pos is None:
            pos = self
        if isinstance(m_or_e, str):
            m_or_e = ParseError(m_or_e, s=pos.s, i=pos.i, **kwargs)
        # otherwise, pos and any kwargs are discarded
        return dataclasses.replace(self, e=m_or_e)


@dataclass
class ASTNode:
    label: typing.Optional[str | type] = field(default=None, kw_only=True)
    children: list[object] = field(default_factory=list, kw_only=True) # should be list[ASTNode], but that fails to parse
    state: ParseState = field(default_factory = lambda: ParseState(None), kw_only=True)
    __match_args__ = ("label", "children")

    _no_parse = {'label', 'children', 'state'}

    def __post_init__(self):
        if (l := getattr(self, 'class_label', None)):
            self.label = l
        self.map = {v.label: v for v in self.children if isinstance(v, ASTNode) and v.label is not None}
        self._sub_fields = tuple(f for f in fields(self) if f.name not in self._no_parse)

    @property
    def s(self):
        return self.state.s

    @property
    def i(self):
        return self.state.i

    def finalize(self):
        if isinstance(self.label, type):
            return self.label.from_ast(self)
        else:
            return self

    def label_name(self):
        if self.label is None:
            return "anonymous parse unit"
        else:
            return f"`{self.label}`"

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
            raise ParseError(error, s=self.state.s, i=self.state.i)
        else:
            return default

    def left_extend(self, node):
        # assumption: `node` comes from a substring that is linearly to the left
        # of self, and we should use node's s/i values
        return ASTNode(label=self.label, children=(node.children + self.children), state=node.state)

    def right_extend(self, node):
        return ASTNode(label=self.label, children=(self.children + node.children), state=self.state)

    def left_attach(self, node):
        # assumption: `node` comes from a substring that is linearly to the left
        # of self, and we should use node's s/i values
        if node.label is None:
            return self.left_extend(node)
        else:
            return ASTNode(label=self.label, children=([node] + self.children), state=node.state)

    def right_attach(self, node):
        if node.label is None:
            return self.right_extend(node)
        else:
            return ASTNode(label=self.label, children=(self.children + [node]), state=self.state)

    def __contains__(self, x):
        return x in self.map

    def __len__(self):
        return len(self.children)

    def null(self):
        # the label check should filter out all subclass instances...
        return self.label is None and len(self.children) == 0

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
            assert 'language' in kwargs # TODO remove or clean up
            return self.children[0].instantiate(**kwargs)

        # if this shows up, it's a parser bug
        raise NotImplementedError(f"Don't know how to instantiate generic ASTNode: {repr(self)}")

    @classmethod
    def map_from_ast(cls, a, allow_remainder=False, state=None):
        if a is None:
            return cls(state=state) # may error

        # currently these params are unused except for the None case, but
        # do this to be robust
        if state is None:
            state = a.state
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
                raise ParseError(f"Internal parser error: parsing to `{cls}` failed to consume fields: `{', '.join(missing)}`", s=state.s, i=state.i)
        return cls(state=state, **m)

    @classmethod
    def seq_from_ast(cls, a, ast_constraint=None, state=None, **fields):
        if a is None:
            return cls(state=state, **fields)
        if state is None:
            state = a.state
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
                        state = x.state
                    raise ParseError(f"Failed to match `{ast_constraint.class_label}` in `{a.label}`",
                        s=state.s, i=state.i)
        return cls(children=children, state=state, **fields)

    @classmethod
    def from_ast(cls, a, state=None):
        # default is the most flexible parsing option: any fields in a subclass
        # are parsed, and the remainder is inserted into `children`.
        return cls.map_from_ast(a, allow_remainder=True, state=state)


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


def seq_result(parser, accum, cur, original):
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
        return ASTNode(label=label, children=accum, state=original), cur


def seq_extend(accum, n):
    if n:
        if n.label is None:
            # This will wipe out an unlabeled node with no values
            accum.extend(n.children)
        else:
            accum.append(n)


class Parselet(object):
    parser = None
    name = None
    def __init__(self, parser, ast_label=None, error=None, skip_trivial=False, name=None):
        if parser is not None:
            # only override class-level field if something non-trivial is
            # provided. This is primarily to support the subclassing behavior
            # of `Unit`.
            self.parser = parser
        self.ast_label = ast_label
        if name is not None:
            self.name = name
        self.error_msg = error
        self.skip_trivial = skip_trivial

    def _repr_pretty_before(self, p, cycle):
        pass

    def _repr_pretty_(self, p, cycle):
        with p.group(2, f"{self.__class__.__name__}(", ")"):
            # p.break_()
            if self.name:
                p.text(f"name=")
                p.pretty(self.name)
                p.text(",")
                if not cycle:
                    p.breakable(sep=" ")
            if self.ast_label:
                p.text(f"ast_label=")
                p.pretty(self.ast_label)
                p.text(",")
                if not cycle:
                    p.breakable(sep=" ")
            if not self.name and not self.ast_label and not cycle:
                p.breakable(sep="")
            if cycle:
                p.text(" ...")
            else:
                self._repr_pretty_before(p, cycle)
                if self.parser is not None:
                    p.pretty(self.parser)

    def copy_args(self):
        return dict(ast_label=self.ast_label, name=self.name, error=self.error_msg, skip_trivial=self.skip_trivial)

    def rule_name(self):
        if self.name is not None:
            return f"rule `{self.name}`"
        elif self.ast_label is None:
            return "anonymous rule"
        elif isinstance(self.ast_label, type):
            return f"rule `{self.ast_label.__name__}`"
        else:
            return f"rule `{self.ast_label}`"

    def default_error(self, state):
        return f"Failed to parse {self.rule_name()}"

    def error(self, state, error=None, **kwargs):
        if error:
            e = error
        elif self.error_msg:
            e = self.error_msg
        else:
            e = self.default_error(state)
        return state.error(e, **kwargs)

    def parse(self, s, i=0):
        n, state = self._parse(ParseState(s=s, i=i))
        if state.e:
            raise state.e
        return n, state

    def _parse(self, state):
        # this code is more general than subclasses, because it allows for
        # wrapping a parsing function
        if self.parser is None:
            # noop succesful parse
            return None, state

        if isinstance(self.parser, Parselet):
            n, cur = self.parser._parse(state)
        else:
            # assumption: a callable parser returns exactly one result n, with
            # an index into the string it is called with
            try:
                n, i = self.parser(state.s, state.i)
            except ParseError as e:
                # abort and roll back parser state
                return None, state.error(e)
            cur = state.update(i)

        if cur.e:
            return None, cur

        if n is None:
            # interpret this case as a consumer-only parse
            return None, cur
        elif self.skip_trivial and isinstance(n, ASTNode):
            return n, cur
        return ASTNode(label=self.ast_label, children=[n], state=state), cur

    def __call__(self, s, i=0):
        return self.parse(s, i=i)

    def __or__(self, other):
        return Disjunctive(self, other)

    def __add__(self, other):
        return Sequence(self, other)

    def __matmul__(self, other):
        return LateDisjunctive(self, other)


class Unit(Parselet):
    def __init__(self, parser=None, **kwargs):
        if parser is not None and self.parser_builder:
            raise ParseError("Internal parser error: `Unit` parser builder subclass has doubly-supplied parser on construction")
        elif self.parser is not None:
            if parser is not None:
                # subclasses will typically not bother with __init__, so validate
                # this case manually
                raise ParseError("Internal parser error: doubly-supplied parser for `Unit` subclass")
            # leave parser defined as a class attribute, by passing None to
            # superclass
        super().__init__(parser, **kwargs)

    def _repr_pretty_(self, p, cycle):
        # explicitly break recursion at all Unit objects
        if isinstance(self.parser, Parselet) and (self.parser.ast_label is not None or self.parser.name is not None):
            p.text(f"{self.__class__.__name__}({self.parser.__class__.__name__}(")
            if self.parser.name is not None:
                p.text("name=")
                p.pretty(self.parser.name)
                p.text(", ")
            if self.parser.ast_label is not None:
                p.text("ast_label=")
                p.pretty(self.parser.ast_label)
                p.text(", ")
            p.text("...))")
        else:
            p.text(f"{self.__class__.__name__}(...)")

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

    def _parse(self, state):
        n, cur = self.get_parser()._parse(state)
        if cur.e:
            return None, cur
        if n is not None:
            n = n.finalize()
        return n, cur


class Failure(Parselet):
    def __init__(self, error, met_preconditions=True, has_preconditions=None, **kwargs):
        self.met_preconditions = met_preconditions
        self.has_preconditions = has_preconditions
        self.error = error
        super().__init__(None)

    def _parse(self, state):
        return None, state.error(self.error,
                                 met_preconditions=self.met_preconditions,
                                 has_preconditions=self.has_preconditions)


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

    def copy(self, defer=None):
        if defer is None:
            defer = self.defer
        label = self.label_class or self.ast_label
        return Label(label, parser=self.parser, force_node=self.force_node, defer=defer)

    def _parse(self, state):
        if self.parser is None:
            n, cur = super()._parse(state)
        else:
            n, cur = self.parser._parse(state)

        if cur.e:
            return None, cur

        if not n:
            if self.force_node:
                if self.label_class:
                    # `from_ast` will need to handle this case. By default:
                    # call label_class's constructor with no arguments.
                    return self.label_class.from_ast(None, state=state), cur
                else:
                    return ASTNode(label=self.ast_label, state=state), cur
            else:
                # consumer-only parse
                return None, cur
        else:
            if n.label is None:
                # relabel an existing None-labeled node
                if self.label_class:
                    n = self.label_class.from_ast(n)
                else:
                    # relabel as a side effect
                    n.label = self.ast_label
                return n, cur
            else:
                # `n` is already labeled, add a new parent
                n = ASTNode(label=self.ast_label, children=[n], state=state)
                if self.label_class:
                    n = self.label_class.from_ast(n)
                return n, cur

    def __add__(self, other):
        if self.label_class:
            l = self.label_class
        else:
            l = self.ast_label
        if self.parser is not None:
            # Note: some potentially counterintuitive behavior if self.parser
            # is also a Label.
            return Label(l, parser=self.parser + other, force_node=self.force_node, defer=self.defer)
        elif isinstance(other, Sequence):
            return Label(l, parser=other.copy(), force_node=self.force_node, defer=self.defer)
        else:
            return Label(l, parser=Sequence(other), force_node=self.force_node, defer=self.defer)


class Optional(Parselet):
    def __init__(self, parser, fully=True, ast_label=None, **kwargs):
        if ast_label is None:
            ast_label = parser.ast_label
        self.fully = fully
        super().__init__(parser, ast_label=ast_label, **kwargs)

    def _parse(self, state):
        n, cur = self.parser._parse(state)
        if cur.e:
            if not self.fully and cur.e.met_preconditions:
                return None, cur
            else:
                # null but succesful consumer-only parse
                return None, state
        return n, cur


class REParselet(Parselet):
    def __init__(self, regex, consume=None, ast_label=None, flags=0, **kwargs):
        if isinstance(regex, REParselet):
            # minimal copy semantics
            regex = regex.raw_regex
        self.raw_regex = regex
        regex = re.compile(regex, flags=flags)
        # by default: consume if there is no label and no capturing groups
        if consume is None:
            consume = not bool(ast_label) and not regex.groups
        self.consume = consume
        super().__init__(regex, ast_label=ast_label, **kwargs)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            super()._repr_pretty_(p, cycle)
        else:
            p.text(f"{self.__class__.__name__}('{self.raw_regex}')")

    def rule_name(self):
        base = super().rule_name()
        if self.name:
            return base
        else:
            return f'{base} `{self.raw_regex}`'

    def default_error(self, state):
        return f"Failed to match pattern for {self.rule_name()}"

    def fullmatch(self, s):
        return self.parser.fullmatch(s)

    def _parse(self, state):
        m = self.parser.match(state.s, state.i)
        if m:
            cur = state.update(m.end())
            if self.consume:
                # preempt any groups
                return None, cur
            # could do something with named groups
            result = m.groups()
            ret_i = state.i
            if result and (test_i := m.start(1)) >= 0:
                # set the ast `i` value based on the group beginning, not the
                # whole match. (XX generalize to multiple groups)
                ret_i = test_i
            elif not result:
                # use entire match
                result = (m.group(),)
            # XX should this use seq_result?
            return ASTNode(label=self.ast_label, children=result, state=state), cur
        else:
            return None, self.error(state)


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

    def _parse(self, state):
        accum = []
        cur = state
        for p in self.parser:
            n, cur = p._parse(cur)
            if cur.e:
                return None, state.error(cur.e)
            seq_extend(accum, n)

        return seq_result(self, accum, cur, state)

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

    def _repr_pretty_before(self, p, cycle):
        with p.group(2, "pre=(", ")"):
            p.pretty(self.pre)
        p.text(",")
        p.breakable(sep=" ")

    def _parse(self, state):
        accum = []
        n, cur = self.pre._parse(state)
        if cur.e:
            # if a sub-parser has set `met_preconditions` explicitly, don't
            # override that. This might be a bit aggressive for general use,
            # but it is well tuned for the cases in the metalanguage parser.
            # one prime example: TypeParseErrors that happen inside a group.
            if not cur.e.has_preconditions:
                cur.e.met_preconditions = False
            cur.e.has_preconditions = True
            return None, cur
        seq_extend(accum, n)

        # XX code dup with superclass
        for p in self.parser:
            n, cur = p._parse(cur)
            if cur.e:
                cur.e.met_preconditions = True
                cur.e.has_preconditions = True
                return None, state.error(cur.e)

            seq_extend(accum, n)

        return seq_result(self, accum, cur, state)

    def copy(self):
        return Precondition(self.pre, main=self.parser, **self.copy_args())


class Repeat(Parselet):
    def __init__(self, parser, allow_empty=True, force_node=True, check_pre=False, **kwargs):
        self.allow_empty = allow_empty
        self.force_node = force_node
        self.check_pre = check_pre
        super().__init__(parser, **kwargs)

    def _parse(self, state):
        accum = []
        cur = state
        found_any = False
        while cur.i < len(cur.s):
            n, cur = self.parser._parse(cur)
            if cur.e:
                if self.check_pre and cur.e.met_preconditions:
                    return None, state.error(cur.e)
                # otherwise, just stop looping
                cur.e = None
                break
            found_any = True
            seq_extend(accum, n)
        if not self.allow_empty and not found_any:
            return None, state.error(f"Failed to match any instances of `{self.ast_label}`")
        return seq_result(self, accum, cur, state)


class Join(Parselet):
    # basically equivalent to elem + Repeat(join + elem), but it produces a
    # flat ast (and has some more bells and whistles)
    def __init__(self, join, elem,
                allow_empty=True, allow_final=False, initial_join=False,
                label_single=False, force_node=True, empty_error=None,
                **kwargs):
        self.join = join
        self.elem = elem
        self.allow_empty = allow_empty and not empty_error
        self.empty_error = empty_error
        self.allow_final = allow_final
        self.initial_join = initial_join
        self.label_single = label_single
        self.force_node = force_node
        super().__init__([join, elem], **kwargs)

    def _parse(self, state):
        accum = []
        cur = state
        found_any = False
        join_last = False
        if self.initial_join:
            # if this is set, we are expecting the string to *start* with the
            # join.
            n, cur = self.join._parse(cur)
            if cur.e:
                if self.allow_empty:
                    # nothing parsed, treat it as an allowed empty sequence
                    cur.e = None
                    return seq_result(self, accum, cur, state)
                else:
                    return None, cur # pos should be still rewound
            seq_extend(accum, n)
            join_last = True

        while cur.i < len(cur.s):
            n, cur = self.elem._parse(cur)
            if cur.e:
                if not found_any and not self.allow_empty:
                    # we have errored while parsing the first instance of
                    # elem and do not allow empty matches; use the error from
                    # cur rather than the generic empty error
                    return None, state.error(cur.e)
                if cur.e.has_preconditions and cur.e.met_preconditions:
                    # we failed while already committed to elem
                    return None, state.error(cur.e)
                # otherwise, stop looping
                cur.e = None
                break

            seq_extend(accum, n)
            found_any = True
            join_last = False

            join_cur = cur
            n, cur = self.join._parse(cur)
            if cur.e:
                # roll back to cur and stop looping
                cur.e = None
                break
            seq_extend(accum, n)
            join_last = True

        if not found_any and not self.allow_empty:
            if self.empty_error:
                error_msg = self.empty_error
            else:
                error_msg = f"Failed to match any instances of `{self.ast_label}`"
            return None, state.error(error_msg)
        if join_last and not self.allow_final:
            if self.join.ast_label is not None:
                join_name = f"`{self.join.ast_label}`"
            else:
                join_name = "join"
            return None, state.error(
                f"Parsing sequence {self.rule_name()} ended in invalid final {join_name}",
                pos=join_cur)
        return seq_result(self, accum, cur, state)


class Disjunctive(Parselet):
    def __init__(self, *parsers, **kwargs):
        super().__init__(list(parsers), **kwargs)

    def default_error(self, state):
        return f"Failed to find disjunct for {self.rule_name()}"

    def copy(self):
        return Disjunctive(*self.parser, **self.copy_args())

    def _parse(self, state):
        for p in self.parser:
            n, cur = p._parse(state)
            if cur.e:
                if cur.e.met_preconditions:
                    return None, cur
                # otherwise, try again with the next parser
                continue
            if not n:
                # interpret this as a succesful consumer-only parse
                return None, cur
            # only label if this parser explicitly provides a label.
            if self.ast_label is None:
                return n, cur
            else:
                return ASTNode(label=self.ast_label, children=[n], state=state), cur
        # if we get to here, all parsers raised with met_preconditions=False.
        # send that same flag upwards in case this is part of another
        # Disjunctive
        return None, self.error(state, met_preconditions=False)

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
    def __init__(self, prefix, *parsers, defer=False, **kwargs):
        # wrapping this in a Precondition is a bit heavy-handed, but it is
        # guaranteed to do what we want
        if not isinstance(prefix, Precondition):
            prefix = Precondition(prefix)
        self.prefix = prefix
        self.defer = defer

        # some code to handle labeling with stacked LateDisjunctives.
        parsers = [x.copy(defer=True) if deferrable(x) else x for x in parsers]
        # n.b. prefix is not stored in `self.parser`
        super().__init__(parsers, **kwargs)

    def _repr_pretty_before(self, p, cycle):
        with p.group(2, "prefix=(", ")"):
            p.pretty(self.prefix)
        p.text(",")
        p.breakable(sep=" ")

    def default_error(self, state):
        return f"Failed to find late disjunct for {self.rule_name()}"

    def copy(self, defer=None):
        if defer is None:
            defer = self.defer
        return LateDisjunctive(self.prefix, *self.parser, defer=defer, **self.copy_args())

    def _parse(self, state):
        # XX sometimes exceptions from this call may appear somewhat unrelated
        prefix_n, cur_prefix = self.prefix._parse(state)
        if cur_prefix.e:
            return None, cur_prefix
        for p in self.parser:
            disj_n, cur = p._parse(cur_prefix)
            if cur.e:
                if cur.e.met_preconditions:
                    cur.e.has_preconditions = True
                    return None, state.error(cur.e)
                # otherwise, try again from cur_prefix with the next parser
                continue

            if not disj_n or disj_n.null():
                result = prefix_n
            elif not prefix_n or prefix_n.null():
                result = disj_n
            else:
                # both non-null
                result = disj_n.left_attach(prefix_n)

            if result and not self.defer:
                result = result.finalize()
            if not result:
                # interpret this as a succesful consumer-only parse
                return None, cur
            # same labeling logic as Disjunctive at this point
            elif self.ast_label is None:
                return result, cur
            else:
                return ASTNode(label=self.ast_label, children=[result], state=state), cur
        # if we get to here, all parsers raised with met_preconditions=False.
        # send that same flag upwards in case this is part of another
        # Disjunctive
        # n.b. an empty self.parser errors...
        return None, self.error(state, met_preconditions=False)

    def __matmul__(self, other):
        if deferrable(other):
            other = other.copy(defer=True)
        r = self.copy()
        r.parser.append(other)
        return r


def deferrable(x):
    return isinstance(x, LateDisjunctive) or isinstance(x, Label)


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
        parsers = [x.copy(defer=True) if deferrable(x) else x for x in parsers]
        parser = Repeat(Disjunctive(*parsers), check_pre=True)
        super().__init__(parser, **kwargs)

    def _repr_pretty_before(self, p, cycle):
        with p.group(2, "prefix=(", ")"):
            p.pretty(self.prefix)
        p.text(",")
        p.breakable(sep=" ")

    def ast_group_left(self, a):
        if len(a) <= 1:
            return a
        ast = a[0]
        for i in range(1, len(a)):
            ast = ASTNode(label=a[i].label, children=[ast] + a[i].children, state=a[i].state).finalize()
        return [ast]

    def _parse(self, state):
        cur = state
        accum = []
        prefix_n, cur = self.prefix._parse(cur)
        if cur.e:
            return None, cur
        seq_extend(accum, prefix_n)
        n, cur = self.parser._parse(cur)
        if cur.e:
            return None, state.error(cur.e)
        seq_extend(accum, n)
        if not accum:
            return None, cur
        else:
            return seq_result(self, self.ast_group_left(accum), cur, state)


def te_only(env):
    """Ensure that env is a 'pure' expression assignment -- exclude anything but
    TypedExprs."""
    return {key: env[key] for key in env if is_te(env[key])}


# wrap other exception types in ParseError with designated parameters
@contextmanager
def parse_error_wrap(msg, wrap_all=True, **kwargs):
    from lamb.types import TypeParseError, TypeMismatch
    try:
        yield
    except (TypeParseError, TypeMismatch) as e:
        if not wrap_all:
            raise e
        kwargs['e'] = e
        raise ParseError(msg, **kwargs).with_traceback(e.__traceback__) from None
    except ParseError as e:
        if not e.msg:
            e.msg = msg # this should essentially not trigger ever?

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


def remove_comments(s):
    """remove comments (prefaced by #) from a single line"""
    r = s.split("#")
    return r[0].rstrip()


def html_output(accum):
    # legacy function, maybe remove at some point
    x = utils.Namespace(accum)
    return utils.show(markdown=x._repr_markdown_(), plain=repr(x))

# can this be removed? Does anyone or anything use it?
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
