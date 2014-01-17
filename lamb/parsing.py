import sys, re, traceback, collections
from lamb import utils, tree_mini
from lamb.utils import *

#class ParseError(Exception):
#    pass

class ParseError(Exception):
    def __init__(self, msg, s, i, met_preconditions=True):
        self.s = s
        self.i = i
        self.msg = msg
        self.met_preconditions = met_preconditions # set to False to indicate that a try_parse function did not find preconditions for what it is supposed to consume

    def __str__(self):
        if self.s is None:
            return msg
        if self.i is None:
            return "%s, in string '%s'" % (self.msg, self.s)
        elif self.i >= len(self.s):
            return "%s, at point '%s!here!" % (self.msg, self.s)
        else:
            return "%s, at point '%s!here!%s'" % (self.msg, self.s[0:self.i], self.s[self.i:])


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
    """Ensure that env is a 'pure' variable assignment -- exclude anything but TypedExprs."""
    from lamb import meta
    env2 = {key: env[key] for key in env.keys() if isinstance(env[key], meta.TypedExpr)}
    return env2

def parse_equality_line(s, env=None):
    from lamb import meta, lang, types
    # TODO should this go by lines....
    if env is None:
        env = dict()
    var_env = vars_only(env)
    system = lang.get_system()
    a_ctl = system.assign_controller
    l = s.split("=", 1)
    if len(l) != 2:
        raise ParseError("Missing =") # TODO expand
    # right side should be typed expr no matter what

    left_s = l[0].strip()
    match = re.match(r'^\|\|([a-zA-Z0-9]+)\|\|$', left_s)
    if match:
        default = a_ctl.default()
        db_env = default.modify(var_env)
        right_side = meta.TypedExpr.factory(l[1].strip(), assignment=db_env)
        right_side = right_side.under_assignment(db_env)
        #print("assignment is " + str(db_env))
        #print("default is " + str(db_env))
        #print("env is " + str(var_env))

        # lexical assignment
        lex_name = match.group(1)
        item = lang.Item(lex_name, right_side)
        # TODO: add to composition system's lexicon?  Different way of tracking lexicons?
        env[lex_name] = item
        return ({lex_name: item}, env)
    else:
        right_side = meta.TypedExpr.factory(l[1].strip(), assignment=var_env)
        right_side = right_side.under_assignment(var_env)

        # variable assignment case
        # don't pass assignment here, to allow for redefinition.  TODO: revisit
        term = meta.TypedExpr.term_factory(left_s)
        if not term.variable():
            raise ParseError("Assignment to non-variable term")
        ts = meta.get_type_system()
        (unify_l, unify_r) = ts.local_unify(term.type, right_side.type)
        # there are two ways in which unify could fail.  One is the built-in ad hoc type_guessed flag, and one is a genuine type mismatch.
        # we want to silently override guessed types here.
        if unify_l is None:
            if term.type_guessed:
                term.type = right_side.type
            else:
                raise types.TypeMismatch(term, right_side, "Variable assignment")
        else:
            # brute force
            term.type = unify_r
        # NOTE side-effect here
        env[term.op] = right_side
        return ({term.op : right_side}, env)

def remove_comments(s):
    """remove comments (prefaced by #) from a single line"""
    r = s.split("#")
    return r[0]

def parse_line(s, env=None):
    if env is None:
        env = dict()
    try:
        s = remove_comments(s)
        if len(s.strip()) > 0:
            (accum, env) = parse_equality_line(s, env)
            return (accum, env)
        else:
            return (dict(), env)
    except Exception as e:
        #print(e)
        #traceback.print_exc()
        try:
            exec(s, globals(), env)
        except Exception as e2:
            print("Parsing failed with exception:")
            print(e)
            print("Exec failed also:")
            traceback.print_exc()
        return (dict(), env)


def parse_lines(s, env=None):
    if env is None:
        env = collections.OrderedDict()
    accum = collections.OrderedDict()
    lines = s.splitlines()
    for l in lines:
        (a, env) = parse_line(l, env)
        accum.update(a)
    return (accum, env)

def parse(s, state=None):
    return parse_lines(s, state)

def fullvar(d, s):
    from lamb import meta
    if isinstance(s, meta.TypedTerm):
        return s
    else:
        return meta.TypedTerm(s, d[s].type)

def latex_output(accum, env):
    from lamb import meta, lang
    lines = list()
    for k in accum.keys():
        if isinstance(accum[k], meta.TypedExpr):
            lines.append(ensuremath(fullvar(accum, k)._repr_latex_() + "\\:=\\:" + accum[k]._repr_latex_()))
        elif isinstance(accum[k], lang.Item):
            # item will automatically print an equality statement
            lines.append(ensuremath(accum[k]._repr_latex_()))
        else:
            print("(Unknown) %s \\:=\\: %s" % (k, accum[k]))
    return MiniLatex("<br />\n".join(lines))

def parse_qtree(s, i=0):
    s = s.strip()
    r, i = parse_qtree_r(s, i)
    return r

def consume_curly_bracketed(s, i):
    """Parse a balanced expression with curly braces.  Accept any character inside the curly braces."""
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
    # this is a bit hacky, maybe want to generalize to strings that may involve curly braces
    if s[i] == "{":
        return consume_curly_bracketed(s, i)
    elif s[i] == "[":
        return parse_qtree_r(s, i)
    else: # should be just a string
        m_group, new_i = consume_pattern(s, i, r'([a-zA-Z0-9\(\)\:\-]*)')
        if m_group is None or len(m_group) == 0:
            # redundant given the current regex but keeping it in case I want to change that
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
    return (tree_mini.Tree(label, children=children), i)


def parse_paren_str(s, i, balance=0):
    accum = ""
    seq = list()
    start_i = i
    while i < len(s):
        if s[i] == "(":
            i += 1
            r, new_i = parse_paren_str(s, i, balance + 1)
            if len(accum) > 0:
                seq.append(accum)
                accum = ""
            seq.append(r)
            i = new_i
        elif s[i] == ")":
            if balance > 0:
                i += 1
                if len(accum) > 0:
                    seq.append(accum)
                    accum = ""
                return (seq, i)
            else:
                raise ParseError("Unbalanced '(...)' expression", s, i)
        else:
            accum += s[i]
            i += 1
    if len(accum) > 0:
        seq.append(accum)
    if balance != 0:
        raise ParseError("Unbalanced '(...)' expression at end of string", s, i)
    return (seq, i)

def macro_parse_r(struc, parse_fun, h, vnum=1, vprefix="ilnb", always_var=True):
    s = ""
    for sub in struc:
        if isinstance(sub, str):
            s += sub 
        else:
            (sub_str, new_hash, vnum) = macro_parse_r(sub, parse_fun, h, vnum, vprefix=vprefix, always_var=always_var)
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
    vnum = 1
    vprefix = "ilnb"
    (struc, i) = parse_paren_str(s, 0)
    (s, h, vnum) = macro_parse_r(struc, parse_fun, dict(), vnum, vprefix)
    result = parse_fun(s, locals=h)
    return result










