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
def parsing_ts():
    from lamb.meta import get_type_system
    return get_type_system()

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
def try_parse():
    try:
        yield
    except ParseError as e:
        if not e.met_preconditions:
            return None
        else:
            raise e


def consume_char(s, i, match, error=None):
    if i >= len(s):
        if error is not None:
            raise ParseError(error, s, i)
        else:
            return None
    if s[i] == match:
        return i + 1
    else:
        if error is None:
            return None
        else:
            raise ParseError(error, s, i)

def consume_pattern(s, i, regex, error=None, return_match=False, **kwargs):
    if i > len(s):
        if error is not None:
            raise ParseError(error, s=s, i=i, **kwargs)
        else:
            return (None, None)
    m = re.match(regex, s[i:])
    if m:
        if return_match:
            return (m, m.end() + i)
        else:
            return (m.group(), m.end() + i)
    else:
        if error is None:
            return (None, None)
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

def consume_whitespace(s, i, error=None):
    m_group, i = consume_pattern(s, i, r'\s*', error)
    return i

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


def try_parse_item_name(s, env=None, ambiguity=False):
    match, i = consume_pattern(s, 0,
                r'^\s*\|\|([a-zA-Z _]+[a-zA-Z0-9 _]*)(\[-?([0-9]+|\*)\])?\|\|',
                return_match=True)
    if not match:
        return (None, None, None)
    lex_name = match.group(1).replace(" ", "_")
    if lex_name != match.group(1):
        logger().info("Exporting item ||%s|| to python variable `%s`."
                                % (match.group(1), lex_name))
    index = None
    index_str = match.group(2)
    if not index_str or len(index_str) == 0 or index_str == "[*]":
        if (lex_name in env.keys() and (ambiguity or index_str == "[*]")):
            index = True
        else:
            index = None # override existing item or add a new one
    else:
        index = int(index_str[1:-1])
    return (lex_name, index, i)


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


def parse_assign_op(s, i, met_preconditions=False):
    # parse the `=` in the middle of an assignment line
    m, i = consume_pattern(s, i, r'^\s*=(?:<([a-zA-Z0-9_]*)>)?\s*',
                    return_match=True,
                    met_preconditions=met_preconditions,
                    error="Missing `=` in assignment")
    if m.group(1):
        # transform name
        return m.group(1), i
    else:
        return None, i


def valid_op_symbol(s):
    from lamb.meta.core import is_op_symbol
    return is_op_symbol(s) or re.match(match_term_re, s) is not None


def parse_op_assign(s, env, var_env, transforms=None):
    from lamb.meta.core import op_from_te, registry
    _, i = consume_pattern(s, 0, 'operator ',
                    error="Missing `operator`", met_preconditions=False)
    # this massively over-accepts compared to what is supported, but it makes
    # error messaging easier later. Similarly for arity.
    op_i = i
    m, i = consume_pattern(s, i, r'^([a-zA-Z0-9_!@%^&*~<>:|\\/?\-=+]+)(?:\((\d+)\))?',
                    return_match=True,
                    error=f"Invalid operator name in `{s}`",
                    met_preconditions=False)
    op_symbol = m.group(1)
    # note: the above pattern will greedily match =, so a space is needed for
    # some operator symbols
    transform, i = parse_assign_op(s, i)

    if not valid_op_symbol(op_symbol):
        raise ParseError(f"Invalid operator symbol `{op_symbol}`", s=s, i=op_i)

    var_env = vars_only(env)
    right_side = parse_right(op_symbol, s[i:], var_env, constants=True)
    if right_side is None:
        return ({}, env)
    right_side = apply_rs_transform(right_side, transform, transforms=transforms)
    if m.group(2):
        op_arity = int(m.group(2)) # should be safe given a succesful match
    else:
        op_arity = None # autodetect
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


def parse_var_assign(s, env, var_env, transforms=None):
    # this overaccepts here
    left_s, i = consume_pattern(s, 0, r'^\s*([a-zA-Z0-9_]+)',
        error="Invalid variable name in assignment",
        met_preconditions=False)
    transform, i = parse_assign_op(s, i)
    right_side = parse_right(left_s, s[i:], var_env, constants=True)
    if right_side is None:
        return ({}, env)

    from lamb.meta import TypedExpr
    with error_manager():
        with parse_error_wrap(f"Assignment to `{left_s}` failed"):
            # don't pass assignment here, to allow for redefinition.  TODO: revisit
            term = TypedExpr.term_factory(left_s, typ=right_side.type)
            if term.type != right_side.type:
                # the left-side term parsing resulted in a stronger principal
                # type
                right_side = TypedExpr.ensure_typed_expr(right_side, typ=term.type)

            right_side = apply_rs_transform(right_side, transform, transforms=transforms)

            # NOTE side-effect here
            env[term.op] = right_side
            return ({term.op : right_side}, env)

    # shouldn't be reachable
    return ({}, env)


def parse_lex_assign(s, env, var_env, ambiguity=False, transforms=None):
    from lamb.lang import get_system, Item, Items
    lex_name, item_index, i = try_parse_item_name(s, env=env,
                                                        ambiguity=ambiguity)
    if lex_name is None:
        # XX convert the item name parser to raise directly
        raise ParseError(f"Invalid lexical entry name in `{s}`", met_preconditions=False)

    transform, i = parse_assign_op(s, i)

    a_ctl = get_system().assign_controller
    default = a_ctl.default()
    db_env = default.new_child(var_env)
    right_side = parse_right(lex_name, s[i:], db_env)
    if right_side is None:
        return ({}, env)
    right_side = apply_rs_transform(right_side, transform, transforms=transforms)

    item = Item(lex_name, right_side)
    if item_index is None:
        env[lex_name] = item
    else:
        # item_index is only set to a value if the item already exists in
        # env.
        if isinstance(env[lex_name], Item):
            tmp_list = list([env[lex_name]])
            if item_index is True:
                tmp_list.append(item)
            else:
                tmp_list[item_index] = item # may throw an exception
            item = Items(tmp_list)
            env[lex_name] = item
        else:
            if item_index is True:
                env[lex_name].add_result(item)
            else:
                env[lex_name][item_index] = item
            item = env[lex_name]
    return ({lex_name: item}, env)


def parse_assignment(s, env=None, transforms=None, ambiguity=False):
    # XX this is a standard parsing combinator approach that could be
    # generalized
    var_env = vars_only(env)
    with try_parse():
        return parse_op_assign(s, env, var_env, transforms=transforms)
    with try_parse():
        return parse_var_assign(s, env, var_env, transforms=transforms)
    with try_parse():
        return parse_lex_assign(s, env, var_env, transforms=transforms, ambiguity=ambiguity)

    raise ParseError("Parsing of assignment failed", s)


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


term_symbols_re = r'[a-zA-Z0-9]'
base_term_re = fr'{term_symbols_re}+'
full_term_re = fr'(_?{base_term_re})(_)?'
match_term_re = fr'{base_term_re}$'


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


def parse_term(s, i=0, return_obj=True, assignment=None):
    """Parse position `i` in `s` as a term expression.  A term expression
    is some alphanumeric sequence followed optionally by an underscore and
    a type.  If a type is not specified locally, but is present in 
    `assignment`, use that.  If a type is specified and is present in
    `assignment`, check type compatibility immediately."""

    term_name, next = consume_pattern(s, i, full_term_re, return_match=True)

    if not term_name:
        if return_obj:
            return (None, i)
        else:
            return (None, None, i)
    if term_name.group(2):
        # try to parse a type
        # if there is a _, will force an attempt
        typ, end = parsing_ts().type_parser_recursive(s, next)
    else:
        typ = None
        end = next

    if return_obj:
        from lamb.meta import TypedExpr
        term = TypedExpr.term_factory(term_name.group(1), typ=typ,
                                assignment=assignment, preparsed=True)
        return (term, end)
    else:
        return (term_name.group(1), typ, end)


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


def try_parse_typed_term(s, assignment=None, strict=False):
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
