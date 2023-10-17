import sys, re, traceback, collections
from contextlib import contextmanager

from lamb import utils
from lamb.utils import * # TODO: remove

Tree = utils.get_tree_class()

global eq_transforms
eq_transforms = dict()

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

    def __str__(self):
        # include this in `prefix` so it is counted for positioning an error
        # marker
        m = f"{self.__class__.__name__}: {self.msg}"
        aux = self._aux_str()
        if self.s is None:
            return m + aux
        elif self.i is None:
            return f"{m}, in string `{self.s}`{aux}"
        else:
            return utils.error_pos_str(self.s, self.i, prefix=m,
                                    plain=True, multiline=True)

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
        return self.__str__()


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

def consume_pattern(s, i, regex, error=None, return_match=False):
    if i > len(s):
        if error is not None:
            raise ParseError(error, s, i)
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
            raise ParseError(error, s, i)

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
    from lamb import meta
    env2 = {key: env[key] for key in env.keys()
                                    if isinstance(env[key], meta.TypedExpr)}
    return env2

# wrap other exception types in ParseError with designated parameters
@contextmanager
def parse_error_wrap(msg, paren_struc=None, wrap_all=True, **kwargs):
    from lamb import types
    try:
        yield
    except (types.TypeParseError, types.TypeMismatch) as e:
        if not wrap_all:
            raise e
        kwargs['e'] = e
        # special case this, so that the caller doesn't need to preemptively
        # flatten
        if paren_struc:
            kwargs['s'] = flatten_paren_struc(paren_struc)
        raise ParseError(msg, **kwargs)
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


# generalized context manager for displaying lnb errors in a sensible way. Tries
# to display them, and if not, falls back on logging.
@contextmanager
def error_manager(summary=None):
    from lamb import meta, types
    display = None
    try:
        from IPython.display import display
    except ImportError:
        pass

    try:
        try:
            yield
        except (types.TypeParseError,
                types.TypeMismatch,
                ParseError) as e:
            if not display:
                raise e
            display(e)
    except Exception as e:
        if summary:
            meta.logger.error(summary)
        meta.logger.error(str(e))

def magic_opt(optname, line):
    # simple and dumb, maybe improve some day
    if line.startswith(f"{optname} "):
        return (True, line[len(optname) + 1:])
    else:
        return (False, line)

def parse_te(line, env=None, use_env=False):
    from lamb import meta
    line = remove_comments(line)
    reduce, line = magic_opt("reduce", line)
    simplify, line = magic_opt("simplify", line)

    if env is None or not use_env:
        env = dict()
    var_env = vars_only(env)
    result = None
    with error_manager("Parsing of typed expression failed with exception:"):
        result = meta.te(line, assignment=var_env)
        if isinstance(result, meta.TypedExpr):
            result = result.regularize_type_env(var_env, constants=True)
            # TODO: should calling simplify_all simply entail reduce_all in the
            # first place?
            if reduce or simplify:
                result = result.reduce_all()
            if simplify:
                result = result.simplify_all()
        else:
            pass # warning here?

    accum = dict()
    if result is not None:
        accum["_llast"] = result
    return (result, accum)

def try_parse_item_name(s, env=None, ambiguity=False):
    match = re.match(
                r'^\|\|([a-zA-Z _]+[a-zA-Z0-9 _]*)(\[-?([0-9]+|\*)\])?\|\|$', s)
    if not match:
        return (None, None)
    lex_name = match.group(1).replace(" ", "_")
    if lex_name != match.group(1):
        from lamb import meta
        meta.logger.info("Exporting item ||%s|| to python variable `%s`."
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
    return (lex_name, index)

def parse_right(left_s, right_s, env, constants=False):
    from lamb import meta
    right_side = None
    with error_manager():
        with parse_error_wrap(f"Parsing of assignment to `{left_s}` failed"):
            right_side = meta.te(right_s.strip(), assignment=env)
            right_side = right_side.regularize_type_env(env, constants=constants)
            right_side = right_side.under_assignment(env)

    return right_side

def parse_equality_line(s, env=None, transforms=None, ambiguity=False):
    from lamb import meta, lang, types
    # TODO should this go by lines....
    if env is None:
        env = dict()
    if transforms is None:
        transforms = dict()
    var_env = vars_only(env)
    system = lang.get_system()
    a_ctl = system.assign_controller
    l = s.split("=", 1)
    if len(l) != 2:
        raise ParseError("Missing `=`") # TODO expand
    transform = None
    right_str = l[1]
    if right_str[0] == "<":
        trans_match = re.match(r'^\<([a-zA-Z0-9_]*)\>', right_str)
        if trans_match:
            trans_name = trans_match.group(1)
            if transforms and trans_name in transforms:
                transform = transforms[trans_name]
                right_str = right_str[trans_match.end(0):]
            else:
                raise ParseError("Unknown transform `<%s>`" % (trans_name))
    if transform is None and "default" in transforms:
        transform = transforms["default"]


    # right side should be typed expr no matter what
    left_s = l[0].strip()
    lex_name, item_index = try_parse_item_name(left_s, env=env,
                                                        ambiguity=ambiguity)
    if lex_name:
        default = a_ctl.default()
        db_env = default.modify(var_env)
        right_side = parse_right(left_s, right_str, db_env)
        if right_side is None:
            return (dict(), env)

        # lexical assignment
        if transform:
            right_side = transform(right_side)

        item = lang.Item(lex_name, right_side)
        # TODO: add to composition system's lexicon?  Different way of tracking
        # lexicons?
        if item_index is None:
            env[lex_name] = item
        else:
            # item_index is only set to a value if the item already exists in
            # env.
            if isinstance(env[lex_name], lang.Item):
                tmp_list = list([env[lex_name]])
                if item_index is True:
                    tmp_list.append(item)
                else:
                    tmp_list[item_index] = item # may throw an exception
                item = lang.Items(tmp_list)
                env[lex_name] = item
            else:
                if item_index is True:
                    env[lex_name].add_result(item)
                else:
                    env[lex_name][item_index] = item
                item = env[lex_name]
        return ({lex_name: item}, env)
    else: # assignment to variable
        right_side = parse_right(left_s, right_str, var_env, constants=True)
        if right_side is None:
            return (dict(), env)

        # variable assignment case
        # don't pass assignment here, to allow for redefinition.  TODO: revisit
        term = meta.TypedExpr.term_factory(left_s)
        if not term.variable():
            raise ParseError("Assignment to non-variable term '%s'" % term)
        ts = meta.get_type_system()
        u_result = ts.unify(term.type, right_side.type)
        # there are two ways in which unify could fail.  One is the built-in ad
        # hoc type_guessed flag, and one is a genuine type mismatch. We want to
        # silently override guessed types here.
        if u_result is None:
            if term.type_guessed:
                term.type = right_side.type
            else:
                raise types.TypeMismatch(term, right_side,
                                                        "Variable assignment")
        else:
            # brute force
            term.type = u_result
        if transform:
            right_side = transform(right_side)
        # NOTE side-effect here
        env[term.op] = right_side
        return ({term.op : right_side}, env)

def remove_comments(s):
    """remove comments (prefaced by #) from a single line"""
    r = s.split("#")
    return r[0]

def parse_line(s, env=None, transforms=None, ambiguity=False):
    if env is None:
        env = dict()
    try:
        s = remove_comments(s)
        if len(s.strip()) > 0:
            (accum, env) = parse_equality_line(s, transforms=transforms,
                                                env=env, ambiguity=ambiguity)
            return (accum, env)
        else:
            return (dict(), env)
    except Exception as e:
        from lamb import meta
        meta.logger.error("Parsing failed with exception:")
        meta.logger.error(e)
        
        return (dict(), env)


def parse_lines(s, env=None, transforms=None, ambiguity=False):
    if env is None:
        env = collections.OrderedDict()
    global eq_transforms
    if transforms is None:
        transforms = eq_transforms
    accum = collections.OrderedDict()
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
    from lamb import meta
    if isinstance(s, meta.TypedTerm):
        return s
    else:
        return meta.TypedTerm(s, d[s].type)

def html_output(accum, env):
    from lamb import meta, lang
    lines = []
    plain_lines = []
    if len(accum) == 0:
        # use markdown for consistency...
        return utils.show(markdown="<i>(Empty lexicon)</i>")
    for k in accum.keys():
        if isinstance(accum[k], meta.TypedExpr):
            var = fullvar(accum, k)
            lines.append(ensuremath(var._repr_latex_()
                                    + "\\:=\\:"
                                    + accum[k]._repr_latex_()))
            plain_lines.append(repr(var) + " = " + repr(accum[k]))
        elif isinstance(accum[k], lang.Items):
            # TODO: less ad hoc treatment of this case
            lines.extend(accum[k].all_latex_strs())
        elif isinstance(accum[k], lang.Composable):
            # item will automatically print an equality statement
            lines.append(accum[k]._repr_latex_())
            plain_lines.append(repr(accum[k]))
        else:
            print("(Unknown class '%s') %s \\:=\\: %s" % (accum[k].__class__,
                                                          k, accum[k]))
    return utils.show(markdown="<br />\n".join(lines), plain="\n".join(plain_lines))

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
    """Flatten a parsed structure into a string"""
    s = ""
    for sub in struc:
        if isinstance(sub, str):
            s += sub
        else:
            s += flatten_paren_struc(sub)
    return s.strip()

global brackets, close_brackets
brackets = {"(" : ")"}
close_brackets = {brackets[y] : y for y in brackets.keys()}

def parse_paren_str(s, i, type_sys=None):
    """Turn a string with parenthesis into a structured representation,
    checking balance.

    The structure consists of a list of strings/lists.  Sub-elements that are
    lists have the same structure. Each distinct sub-element represents a
    parenthesized grouping.

    Right now only pays attention to ().  TODO: check other bracketings?"""
    stack = list()
    (seq, i) = parse_paren_str_r(s, i, stack, type_sys=type_sys)
    if len(stack) != 0:
        raise ParseError("Unbalanced '%s...%s' expression at end of string" %
                                    (stack[-1], brackets[stack[-1]]), s, i)
    return (seq, i)


def parse_paren_str_r(s, i, stack, initial_accum=None, type_sys=None):
    accum = ""
    seq = list()
    if initial_accum is not None:
        seq.append(initial_accum)
    start_i = i
    while i < len(s):
        if s[i] == "_" and type_sys != None:
            accum += "_"
            # have to parse type here in order to handle bracketing in types
            # correctly. I don't think there's a shortcut to this.  In the long
            # run, this should do proper tokenizing of terms.
            typ, end = type_sys.type_parser_recursive(s, i+1)
            assert(typ is not None)
            # oh good god
            accum += repr(typ)
            i = end
        elif s[i] in brackets.keys():
            stack.append(s[i])
            i += 1

            r, new_i = parse_paren_str_r(s, i, stack, initial_accum=stack[-1],
                                                            type_sys=type_sys)
            if len(accum) > 0:
                seq.append(accum)
                accum = ""
            seq.append(r)
            i = new_i
        elif s[i] in close_brackets.keys():
            if len(stack) > 0 and s[i] == brackets[stack[-1]]:
                if len(accum) > 0:
                    seq.append(accum)
                    accum = ""
                stack.pop()
                seq.append(s[i])
                i += 1
                return (seq, i)
            else:
                raise ParseError("Unbalanced '%s...%s' expression"
                                        % (close_brackets[s[i]], s[i]), s, i)
        else:
            accum += s[i]
            i += 1
    if len(accum) > 0:
        seq.append(accum)
    return (seq, i)

def macro_parse_r(struc, parse_fun, h, vnum=1, vprefix="ilnb", always_var=True):
    """Proof of concept for parsing paren structures.  Not used generally."""
    s = ""
    for sub in struc:
        if isinstance(sub, str):
            s += sub 
        else:
            (sub_str, new_hash, vnum) = macro_parse_r(sub, parse_fun, h, vnum,
                                        vprefix=vprefix, always_var=always_var)
            h = new_hash
            parsed_sub = parse_fun(sub_str, locals=h)
            if isinstance(parsed_sub, str) and not always_var:
                s += "(" + parsed_sub + ")"
            else:
                var = vprefix + str(vnum)
                s += "(" + var + ")"
                vnum += 1
                h[var]= parsed_sub
    return (s, h, vnum)


def macro_parse(s, parse_fun):
    """Proof of concept for parsing paren structures.  Not used generally."""
    vnum = 1
    vprefix = "ilnb"
    (struc, i) = parse_paren_str(s, 0)
    (s, h, vnum) = macro_parse_r(struc, parse_fun, dict(), vnum, vprefix)
    result = parse_fun(s, locals=h)
    return result
