import keyword, collections
import lamb
from lamb import parsing, utils, lang
from lamb.utils import *

from IPython.core.magic import (Magics, magics_class, line_magic,
                                cell_magic, line_cell_magic)

def check_shadowing(words):
    l = list()
    for k in words:
        if keyword.iskeyword(k):
            l.append(k)
    return l

def process_items(fun, *i, env=None):
    """This function processes one or more lexical entries in various possible
    forms.

    Possible forms: a list of lexical entries, a dict, or a lexicon.
    If the dict contains strs, it tries to use the "env" argument."""
    result = list()
    if len(i) == 0:
        return result
    for item in i:
        if isinstance(item, dict):
            # argument is probably an env or a lexicon dict
            for k in item.keys():
                item[k] = process_items(fun, item[k])[0]
            result.append(item)
        elif isinstance(item, lang.CompositionSystem):
            # Hamblinize an entire lexicon in one shot
            result.append(process_items(fun, item.lexicon)[0])
        elif isinstance(item, str) and env is not None and item in env.keys():
            # for hamblinizing the contents of a dict that maps strings to
            # hamblinizable things
            env[item] = process_items(fun, env[item])[0]
        elif isinstance(item, lang.Item):
            result.append(fun(item))
        else:
            result.append(item) # silently ignore...
    if len(result) == 0:
        return None
    return result


@magics_class
class LambMagics(Magics):
    specials = dict()
    specials_post = dict()
    def __init__(self, shell):
        super(LambMagics, self).__init__(shell)
        self.env = collections.OrderedDict()
        self.silent = False
        self.ambiguity = False
        self.cur_ambiguity = self.ambiguity

    def shadow_warnings(self, dict):
        l = check_shadowing(dict.keys())
        for k in l:
            print("Warning: variable name '%s' is reserved and will be "
                "shadowed in python" % k)

    @line_cell_magic
    def lamb(self, line, cell=None):
        "Magic that works both as %lcmagic and as %%lcmagic"
        self.cur_ambiguity = self.ambiguity
        if cell is None:
            #print("Called as line magic")
            (accum, env) = parsing.parse(line, self.env)
            self.env = env
        else:
            #print("Called as cell magic")
            #return line, cell
            if len(line) > 0:
                r = self.control_line(line)
                if r is not None:
                    return r #TODO fix this up, not right
            (accum, env) = parsing.parse(cell, self.env,
                                                ambiguity=self.cur_ambiguity)
            self.env = env
            self.control_line(line, post=True, accum=accum)
        self.shadow_warnings(accum)
        self.shell.push(accum)
        return parsing.latex_output(accum, self.env)
    
    def reset(self):
        self.env = dict()

    def control_line(self, line, post=False, accum=None):
        args = line.split(",")
        for a in args:
            if post:
                r = self.control_post(a.strip(), accum)
            else:
                r = self.control(a.strip())
            if r is not None:
                return r # TODO: fix
        return None

    def control_post(self, cmd, accum):
        if cmd in self.specials_post:
            return self.specials_post[cmd](self, accum)
        else:
            return None

    def control(self, cmd):
        if cmd == "reset":
            self.reset()
            return None
        elif cmd == "all":
            return parsing.latex_output(self.env, self.env)
        elif cmd == "ambiguity":
            self.cur_ambiguity = True
        else:
            if cmd in self.specials.keys():
                return self.specials[cmd](self)
            else:
                if cmd not in self.specials_post:
                    print("Don't know what to do with '%s'" % cmd)
                return None

    @line_magic
    def lambctl(self, line):
        return self.control_line(line)

    @line_magic
    def te(self, line):
        (result, accum) = parsing.parse_te(line, self.env)
        self.shell.push(accum)
        return result


def setup_magics():
    try:
        ip = get_ipython()
    except: # fail silently if there's no ipython kernel
        return
    ip.register_magics(LambMagics)
    
setup_magics()

