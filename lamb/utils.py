import sys, re, html
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

# Katex autorender code, for use in a colab (Google Colaboratory) iframe.
# this is a tweaked version of https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/contrib/auto-render.min.js
# * enable $ as a delimiter (colab does this already, but katex doesn't by default)
# * add on a render call
# * difference from colab: leave \(\) enabled as delimiters. (Or, maybe these are enabled in colab, but are buggy?)
# In principle, possibly this could be pulled dynamically from a CDN, but it's
# easier / smoother to hardcode it and avoid external dependencies.
katex_autorender_min = (r'''!function(e,t){"object"==typeof exports&&"object"==typeof module?module.exports=t(require("katex")):"function"==typeof define&&define.amd?define(["katex"],t):"object"==typeof exports?exports.renderMathInElement=t(require("katex")):e.renderMathInElement=t(e.katex)}("undefined"!=typeof self?self:this,(function(e){return function(){"use strict";var t={771:function(t){t.exports=e}},r={};function n(e){var i=r[e];if(void 0!==i)return i.exports;var a=r[e]={exports:{}};return t[e](a,a.exports,n),a.exports}n.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return n.d(t,{a:t}),t},n.d=function(e,t){for(var r in t)n.o(t,r)&&!n.o(e,r)&&Object.defineProperty(e,r,{enumerable:!0,get:t[r]})},n.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)};var i={};return function(){n.d(i,{default:function(){return s}});var e=n(771),t=n.n(e),r=function(e,t,r){for(var n=r,i=0,a=e.length;n<t.length;){var o=t[n];if(i<=0&&t.slice(n,n+a)===e)return n;"\\"===o?n++:"{"===o?i++:"}"===o&&i--,n++}return-1},a=/^\\begin{/,o=function(e,t){for(var n,i=[],o=new RegExp("("+t.map((function(e){return e.left.replace(/[-/\\^$*+?.()|[\]{}]/g,"\\$&")})).join("|")+")");-1!==(n=e.search(o));){n>0&&(i.push({type:"text",data:e.slice(0,n)}),e=e.slice(n));var l=t.findIndex((function(t){return e.startsWith(t.left)}));if(-1===(n=r(t[l].right,e,t[l].left.length)))break;var d=e.slice(0,n+t[l].right.length),s=a.test(d)?d:e.slice(t[l].left.length,n);i.push({type:"math",data:s,rawData:d,display:t[l].display}),e=e.slice(n+t[l].right.length)}return""!==e&&i.push({type:"text",data:e}),i},l=function(e,r){var n=o(e,r.delimiters);if(1===n.length&&"text"===n[0].type)return null;for(var i=document.createDocumentFragment(),a=0;a<n.length;a++)if("text"===n[a].type)i.appendChild(document.createTextNode(n[a].data));else{var l=document.createElement("span"),d=n[a].data;r.displayMode=n[a].display;try{r.preProcess&&(d=r.preProcess(d)),t().render(d,l,r)}catch(e){if(!(e instanceof t().ParseError))throw e;r.errorCallback("KaTeX auto-render: Failed to parse `"+n[a].data+"` with ",e),i.appendChild(document.createTextNode(n[a].rawData));continue}i.appendChild(l)}return i},d=function e(t,r){for(var n=0;n<t.childNodes.length;n++){var i=t.childNodes[n];if(3===i.nodeType){for(var a=i.textContent,o=i.nextSibling,d=0;o&&o.nodeType===Node.TEXT_NODE;)a+=o.textContent,o=o.nextSibling,d++;var s=l(a,r);if(s){for(var f=0;f<d;f++)i.nextSibling.remove();n+=s.childNodes.length-1,t.replaceChild(s,i)}else n+=d}else 1===i.nodeType&&function(){var t=" "+i.className+" ";-1===r.ignoredTags.indexOf(i.nodeName.toLowerCase())&&r.ignoredClasses.every((function(e){return-1===t.indexOf(" "+e+" ")}))&&e(i,r)}()}},s=function(e,t){if(!e)throw new Error("No element provided to render");var r={};for(var n in t)t.hasOwnProperty(n)&&(r[n]=t[n]);r.delimiters=r.delimiters||[{left:"$$",right:"$$",display:!0},{left:"\\(",right:"\\)",display:!1},{left:"$",right:"$",display:!1},{left:"\\begin{equation}",right:"\\end{equation}",display:!0},{left:"\\begin{align}",right:"\\end{align}",display:!0},{left:"\\begin{alignat}",right:"\\end{alignat}",display:!0},{left:"\\begin{gather}",right:"\\end{gather}",display:!0},{left:"\\begin{CD}",right:"\\end{CD}",display:!0},{left:"\\[",right:"\\]",display:!0}],r.ignoredTags=r.ignoredTags||["script","noscript","style","textarea","pre","code","option"],r.ignoredClasses=r.ignoredClasses||[],r.errorCallback=r.errorCallback||console.error,r.macros=r.macros||{},d(e,r)}}(),i=i.default}()}));'''
    + "renderMathInElement(document.body);")

# TODO: this class' origins are much earlier in the ipython life cycle, can it
# be modernized to align better with display classes? Or refactored away entirely?
# if multiple args are specified, in Jupyter the priority is
# markdown > html > latex > repr. Note that using html tags in markdown is
# generally safe, but some frontends (*cough* colab) strip a whole bunch of
# formatting. So it won't work for more complex things like derivation trees.
class BaseLNDisplay(object):
    def __init__(self, html = None, latex = None, markdown = None, plain = ""):
        self.latex = latex
        self.html = html
        self.markdown = markdown
        if not plain:
            plain = html or latex or markdown
        self.plain = plain

    def __str__(self):
        return self.plain

    def __repr__(self):
        return self.plain

    def _repr_latex_(self):
        return self.latex

    def _repr_html_(self):
        return self.html

    def _repr_markdown_(self):
        return self.markdown

# this class is only suitable for colab; it requires on colab's idiosyncratic
# combination of iframes and katex rendering for outputs.
class ColabLNDisplay(BaseLNDisplay):
    def __init__(self, html = None, latex = None, markdown = None, plain = ""):
        super().__init__(html, latex, markdown, plain)

    def _ipython_display_(self):
        import IPython.display
        # colab does not render latex in HTML outputs, so we do a complicated
        # maneuver to trigger it manually. It took me *many* tries to find
        # something that works for this purpose. Some notes:
        # * Issue: https://github.com/googlecolab/colabtools/issues/3941
        # * Colab markdown (at least as of mid-2023) does render latex, but
        #   strips html attributes, making it impossible to use for complex
        #   outputs
        # * Every colab output is rendered in its own iframe, "for security",
        #   drastically complicating everything. It's possible to load mathjax
        #   in an iframe, but this is heavy/slow, and not entirely reliable
        #   anyways
        # * within an iframe, colab uses katex (rather than mathjax), for speed.
        #   It injects a minified version of katex, rather than loading it
        #   externally. Calling katex (as far as I can tell) is fairly
        #   integrated with minified parsing code, and I couldn't figure out a
        #   way to trigger colab's katex render code directly. It doesn't load
        #   or call katex autorender.
        # * colab supports ipywidgets, but HTMLMath in particular is broken on
        #   colab (see https://github.com/googlecolab/colabtools/issues/2680)
        #
        # Solution: ensure that colab injects its katex setup, display the
        # HTML output, then inject and call a version of katex autorender.
        if self.html and not self.markdown:
            # This initial dummy call causes colab to inject its katex code into
            # the iframe
            IPython.display.display(IPython.display.Latex(""))
            # now display the actual output
            IPython.display.display(IPython.display.HTML(self.html))
            # finally, inject (and run) the autorender code. This will produce
            # js errors if there is no katex present in the document context!
            IPython.display.display(IPython.display.Javascript(katex_autorender_min))
        else:
            # should work for everything else...
            IPython.display.display(super())

# warning! The value of LNDisplay may change, so it is not recommended to do
# from utils import LNDisplay. Use `show` below instead.
LNDisplay = BaseLNDisplay

def show(**args):
    return LNDisplay(**args)

# TODO: remove, it's only used in a very old demo and a few misc places
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
                    s += html.escape(x)
                else:
                    s += html.escape(repr(x))
        s += "<br />"
    return show(s)

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
