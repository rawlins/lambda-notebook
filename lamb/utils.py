import sys, re
from numbers import Number

class MiniLatex(object):
    def __init__(self, latex_s, plain_s = None):
        self.latex = latex_s
        if plain_s is None:
            self.plain = latex_s
        else:
            self.plain = plain_s

    def __str__(self):
        return self.plain

    def _repr_latex_(self):
        return self.latex

    def __repr__(self):
        return self.latex

def ltx_print(*args):
    s = ""
    for x in args:
        try:
            s += x._repr_latex_()
        except:
            if isinstance(x, str):
                s += x
            else:
                s += repr(x)
        s += "<br />"
    return MiniLatex(s)

# from AIMA utils
def num_or_str(x):
    """The argument is a string; convert to a number if possible, or strip it.
    >>> num_or_str('42')
    42
    >>> num_or_str(' 42x ')
    '42x'
    """
    if isinstance(x, Number): return x
    try:
        return int(x)
    except ValueError:
        try:
            return float(x)
        except ValueError:
            return str(x).strip()

def parens(s):
    # TODO: ensure at most one outer set of parens
    return "(" + s + ")"

def ensuremath(s):
    return "$" + s.replace("$", "") + "$"

def vname_split(vname):
    g = re.match('([a-zA-Z0-9]*[a-zA-Z0]+)([0-9]*)$', vname) # use character classes?
    # 0 in first group exploits greedy match, will collect any leading zeros so "v001" if blocked becomes "v002"
    # TODO make this even better
    if g is None:
        return (vname, '') # TODO:  what are the failure cases for this?
    else:
        return g.groups()

