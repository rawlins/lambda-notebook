import sys, re, cgi
from numbers import Number

global tree_error_printed
tree_error_printed = False
global use_nltk
use_nltk = False # for the moment this is off by default: subprocess in
                 # _repr_png_ seems to have weird behavior with respect to the
                 # python interface process it spawns, leading to unresponsive
                 # interface.  I'm not sure what's going on.
# to turn on full nltk support, call reload_lamb(use_nltk_tree=True)

def get_tree_class():
    if not use_nltk:
        from lamb.tree_mini import Tree
        return Tree
    global tree_error_printed
    try:
        import nltk
        if int(nltk.__version__[0]) < 3:
            if not tree_error_printed:
                print("Old NLTK version found (%s)." % nltk.__version__)
            raise Exception()
        from nltk import Tree
        import lamb.tree_mini
        Tree.build_display_tree = lamb.tree_mini.Tree.build_display_tree
        Tree._repr_latex_ = lamb.tree_mini.Tree._repr_latex_
        return Tree
    except:
        if not tree_error_printed:
            print("Falling back on lamb.tree_mini for Tree support.")
            tree_error_printed = True
        from lamb.tree_mini import Tree
        return Tree

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

    def _repr_html_(self):
        return self.latex

def ltx_print(*args):
    s = ""
    for x in args:
        try:
            s += x._repr_html_()
        except:
            try:
                s += x._repr_latex_()
            except:
                if isinstance(x, str):
                    s += cgi.escape(x)
                else:
                    s += cgi.escape(repr(x))
        s += "<br />"
    return MiniLatex(s)

# from AIMA utils
def num_or_str(x, allow_float=False):
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
        if allow_float:
            try:
                return float(x)
            except ValueError:
                pass
        return str(x).strip()

def dict_latex_repr(d):
    r = list()
    for k in d:
        try:
            k_repr = k.latex_str()
        except AttributeError:
            k_repr = repr(k)
        try:
            val_repr = d[k].latex_str()
        except AttributeError:
            val_repr = repr(d[k])
        r.append("%s: %s" % (k_repr, val_repr))
    return "{" + ", ".join(r) + "}"

def set_latex_repr(d):
    r = list()
    for k in list(d):
        try:
            k_repr = k.latex_str()
        except AttributeError:
            k_repr = repr(k)
        r.append("%s" % (k_repr))
    return "{" + ", ".join(r) + "}"


def parens(s):
    # TODO: ensure at most one outer set of parens
    return "(" + s + ")"

def ensuremath(s):
    return "$" + s.replace("$", "") + "$"

def vname_split(vname):
    # use character classes?
    g = re.match('([a-zA-Z0-9]*[a-zA-Z0]+)([0-9]*)$', vname)
    # 0 in first group exploits greedy match, will collect any leading zeros so
    # "v001" if blocked becomes "v002"
    # TODO make this even better
    if g is None:
        return (vname, '') # TODO:  what are the failure cases for this?
    else:
        return g.groups()

def nltk_tree_wrapper(t):
    try:
        import tkinter
    except:
        return "NLTK cannot draw trees without tkinter"
    tree = "NLTK tree drawing failed, please make sure you have `nltk` installed"
    try:
        import nltk
        tree = nltk.Tree.fromstring(t)
        tree._repr_png_(); # kind of dumb, but test this before returning
    except tkinter.TclError:
        tree = "Cannot use NLTK tree drawing in a headless state"
    except:
        pass

    return tree
