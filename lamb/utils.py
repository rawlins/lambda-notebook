import sys, re, html
import contextlib
import collections.abc
from numbers import Number

global tree_error_printed
tree_error_printed = False
global use_nltk
use_nltk = False # for the moment this is off by default: subprocess in
                 # _repr_png_ seems to have weird behavior with respect to the
                 # python interface process it spawns, leading to unresponsive
                 # interface.  I'm not sure what's going on.
# to turn on full nltk support, call reload_lamb(use_nltk_tree=True)


# output debugging utilities for dealing with recursive calls via indentation
# the following could be made more elegant in various ways, but it gets the
# job done...
_debug_indent = 0
_debug_suppress = False

# reset/decrease applies before the print, increase after
def dbg_print(*args, increase=False, decrease=False, reset=False):
    global _debug_indent, _debug_suppress
    if reset:
        _debug_indent = 0
    if decrease and _debug_indent > 0:
        _debug_indent -= 4
    if args and not _debug_suppress:
        print(" " * _debug_indent, *args)
    if increase:
        _debug_indent += 4


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
# 
# non-minified code: https://github.com/KaTeX/KaTeX/tree/main/contrib/auto-render
# MIT license: https://github.com/KaTeX/KaTeX/blob/main/LICENSE
katex_autorender_min = (r'''!function(e,t){"object"==typeof exports&&"object"==typeof module?module.exports=t(require("katex")):"function"==typeof define&&define.amd?define(["katex"],t):"object"==typeof exports?exports.renderMathInElement=t(require("katex")):e.renderMathInElement=t(e.katex)}("undefined"!=typeof self?self:this,(function(e){return function(){"use strict";var t={771:function(t){t.exports=e}},r={};function n(e){var i=r[e];if(void 0!==i)return i.exports;var a=r[e]={exports:{}};return t[e](a,a.exports,n),a.exports}n.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return n.d(t,{a:t}),t},n.d=function(e,t){for(var r in t)n.o(t,r)&&!n.o(e,r)&&Object.defineProperty(e,r,{enumerable:!0,get:t[r]})},n.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)};var i={};return function(){n.d(i,{default:function(){return s}});var e=n(771),t=n.n(e),r=function(e,t,r){for(var n=r,i=0,a=e.length;n<t.length;){var o=t[n];if(i<=0&&t.slice(n,n+a)===e)return n;"\\"===o?n++:"{"===o?i++:"}"===o&&i--,n++}return-1},a=/^\\begin{/,o=function(e,t){for(var n,i=[],o=new RegExp("("+t.map((function(e){return e.left.replace(/[-/\\^$*+?.()|[\]{}]/g,"\\$&")})).join("|")+")");-1!==(n=e.search(o));){n>0&&(i.push({type:"text",data:e.slice(0,n)}),e=e.slice(n));var l=t.findIndex((function(t){return e.startsWith(t.left)}));if(-1===(n=r(t[l].right,e,t[l].left.length)))break;var d=e.slice(0,n+t[l].right.length),s=a.test(d)?d:e.slice(t[l].left.length,n);i.push({type:"math",data:s,rawData:d,display:t[l].display}),e=e.slice(n+t[l].right.length)}return""!==e&&i.push({type:"text",data:e}),i},l=function(e,r){var n=o(e,r.delimiters);if(1===n.length&&"text"===n[0].type)return null;for(var i=document.createDocumentFragment(),a=0;a<n.length;a++)if("text"===n[a].type)i.appendChild(document.createTextNode(n[a].data));else{var l=document.createElement("span"),d=n[a].data;r.displayMode=n[a].display;try{r.preProcess&&(d=r.preProcess(d)),t().render(d,l,r)}catch(e){if(!(e instanceof t().ParseError))throw e;r.errorCallback("KaTeX auto-render: Failed to parse `"+n[a].data+"` with ",e),i.appendChild(document.createTextNode(n[a].rawData));continue}i.appendChild(l)}return i},d=function e(t,r){for(var n=0;n<t.childNodes.length;n++){var i=t.childNodes[n];if(3===i.nodeType){for(var a=i.textContent,o=i.nextSibling,d=0;o&&o.nodeType===Node.TEXT_NODE;)a+=o.textContent,o=o.nextSibling,d++;var s=l(a,r);if(s){for(var f=0;f<d;f++)i.nextSibling.remove();n+=s.childNodes.length-1,t.replaceChild(s,i)}else n+=d}else 1===i.nodeType&&function(){var t=" "+i.className+" ";-1===r.ignoredTags.indexOf(i.nodeName.toLowerCase())&&r.ignoredClasses.every((function(e){return-1===t.indexOf(" "+e+" ")}))&&e(i,r)}()}},s=function(e,t){if(!e)throw new Error("No element provided to render");var r={};for(var n in t)t.hasOwnProperty(n)&&(r[n]=t[n]);r.delimiters=r.delimiters||[{left:"$$",right:"$$",display:!0},{left:"\\(",right:"\\)",display:!1},{left:"$",right:"$",display:!1},{left:"\\begin{equation}",right:"\\end{equation}",display:!0},{left:"\\begin{align}",right:"\\end{align}",display:!0},{left:"\\begin{alignat}",right:"\\end{alignat}",display:!0},{left:"\\begin{gather}",right:"\\end{gather}",display:!0},{left:"\\begin{CD}",right:"\\end{CD}",display:!0},{left:"\\[",right:"\\]",display:!0}],r.ignoredTags=r.ignoredTags||["script","noscript","style","textarea","pre","code","option"],r.ignoredClasses=r.ignoredClasses||[],r.errorCallback=r.errorCallback||console.error,r.macros=r.macros||{},d(e,r)}}(),i=i.default}()}));'''
    + "renderMathInElement(document.body);")

# Wrapper class to bridge various possible lambda notebook complex display
# objects to output. This is itself a light object that stores only strings,
# though on creation it will need to generate all the reprs that it is provided.
# arguments can be either strings, or objects that define the relevant repr
# method.
#
# if multiple args are specified, in Jupyter the display priority is
# markdown > html > latex > repr. Note that using html tags in markdown is
# generally safe, but some frontends (*cough* colab) strip a whole bunch of
# formatting. So that won't work for more complex things like derivation trees.
#
# TODO: this class' origins are much earlier in the ipython life cycle, can it
# be modernized to align better with display classes? Or refactored away
# entirely? One possibility for future investigation is to use ipywidgets for
# some or all of this, e.g. HTMLMath. (But, this widget doesn't work on colab.)
class BaseLNDisplay(object):
    def __init__(self, html = None, latex = None, markdown = None, plain = ""):
        # if `latex` (etc) is not a str, try to extract a repr in an intelligent
        # way. Failures here are silent, but they'll typically lead to IPython
        # crashes. (TODO: fail here?)
        self.latex = latex
        if latex is not None and not isinstance(latex, str):
            try:
                self.latex = latex._repr_latex_()
            except AttributeError:
                pass
        self.html = html
        if html is not None and not isinstance(html, str):
            try:
                self.html = html._repr_html_()
            except AttributeError:
                pass

        self.markdown = markdown
        if markdown is not None and not isinstance(markdown, str):
            try:
                self.markdown = markdown._repr_markdown_()
            except AttributeError:
                pass
        if not plain:
            # try to ensure that *something* is present for plain; this will
            # result in fairly unreadable reprs in some cases
            plain = self.markdown or self.latex or self.html
        elif not isinstance(plain, str):
            # this should unconditionally work, though who knows what it'll get
            # in the general case
            plain = repr(plain)
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
    # TODO: arg order for non kw cases?
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



# This is more or less the recipe from:
#    https://github.com/microsoft/vscode/issues/203725#issuecomment-2217367218
# I've been unable to get any fully local solution to work, but I hope that
# VSCode might at least cache this...
# Also, the defaults don't support $ so tweaking delimiters is necessary
vscode_katex = r"""<script type="module">import renderMathInElement from "https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.mjs";renderMathInElement(document.body, {delimiters: [{left: '$$', right: '$$', display: true}, {left: '$', right: '$', display: false}, {left: '\\(', right: '\\)', display: false}, {left: '\\[', right: '\\]', display: true}]});"""


class VSCodeLNDisplay(BaseLNDisplay):
    def __init__(self, html = None, latex = None, markdown = None, plain = ""):
        super().__init__(html, latex, markdown, plain)

    def _ipython_display_(self):
        import IPython.display
        # VSCode uses katex exclusively, but is very inconsistent about
        # triggering a render.
        IPython.display.display(super())
        if self.html or self.markdown:
            IPython.display.display(IPython.display.HTML(vscode_katex))


# warning! The value of LNDisplay may change, so it is not recommended to do
# from utils import LNDisplay. Use `show` below instead.
LNDisplay = BaseLNDisplay

def show(*args, **kwargs):
    return LNDisplay(*args, **kwargs)


def error_pos_str(s, i, prefix="", multiline=False, plain=True):
    i = max(0, min(i, len(s)))
    if len(prefix) and not prefix[-1] == " ":
        prefix += ": "
    if not plain:
        multiline = True
    if multiline:
        if plain:
            i += len(prefix)
            base = f"`{s}`\n {' ' * i}^"
        else:
            base = f"\n```\n    '{s}'\n {' ' * (i + 4)}^\n```"
    else:
        if i >= len(s):
            base = f"`{s}`!here!"
        else:
            base = f"`{s[0:i]}!here!{s[i:]}`"
    return f"{prefix}{base}"

# This is here only for compatibility with the 2013 LSA demo notebook, you
# should just use `IPython.display.display` instead
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


def latex_repr(x, **kwargs):
    """Given some (possibly structured) object `x`, return a MathJax-compatible
    output that renders `x`. If `x` is a set or a dict, will recurse into `x`
    and use `dict_latex_repr` and `set_latex_repr`. Tries `latex_str`, falling
    back on plain `repr`.

    Parameters
    ----------
    x : Any
        An object to render.
    **kwargs : dict, optional
        options for recursive calls

    See also
    --------
    `dict_latex_repr`, `set_latex_repr`
    """
    # supports recursing into dicts and sets
    if isinstance(x, str):
        return x
    # XX try latex_str() first?
    elif isinstance(x, collections.abc.Mapping):
        # or collections.abc.Mapping?
        return dict_latex_repr(x, **kwargs)
    elif isinstance(x, collections.abc.Set):
        return set_latex_repr(x, **kwargs)
    else:
        try:
            return x.latex_str(**kwargs)
        except AttributeError:
            return repr(x)


def dict_latex_repr(d, linearized=True, **kwargs):
    """Given some mapping `d`, render `d` into MathJax-compatible latex code.
    Recurses into the dict using `latex_repr`.

    Parameters
    ----------
    d: collections.abc.Mapping
        a mapping to render
    linearized: bool, default: True
        if ``True``, render in a linearized curly-braced base notation. If
        ``False``, render using a multi-line array.
    **kwargs : dict, optional
        options for recursive calls

    See also
    --------
    `set_latex_repr`, `latex_repr`
    """
    r = list()
    for k in d:
        k_repr = latex_repr(k, linearized=linearized, **kwargs)
        val_repr = latex_repr(d[k], linearized=linearized, **kwargs)
        r.append((k_repr, val_repr))
    if linearized:
        # write this as a fancy dict, basically
        # XX should this use \{\} + ensuremath?
        r = [f"{e[0]}: {e[1]}" for e in r]
        return ensuremath(f"\\{{{', '.join(r)}\\}}")
    elif len(r) == 0:
        return "[]"
    elif len(r) == 1:
        # the array version has ugly whitespace for 1-line dicts
        return ensuremath(f"\\left[{r[0][0]} \\rightarrow {r[0][1]}\\right]")
    else:
        r = '\n'.join([f"{e[0]} & \\rightarrow & {e[1]} \\\\" for e in r])
        return ensuremath(
            # some formatting tweaks that would improve this, e.g. `@{ }`, are
            # not supported by mathjax
            # XX katex compat?
            f"\\left[\\begin{{array}}{{lll}} {r} \\end{{array}}\\right]")


def set_latex_repr(d, set_sorted=True, **kwargs):
    """Given some set `d`, render `d` into MathJax-compatible latex code.
    Recurses into the collection using `latex_repr`.

    Parameters
    ----------
    d: collections.abc.Set
        a set to render
    **kwargs : dict, optional
        options for recursive calls

    See also
    --------
    `dict_latex_repr`, `latex_repr`
    """
    def elem_key(x):
        if isinstance(x, str):
            return x
        else:
            return x.op
    r = list()
    if set_sorted:
        try:
            d = sorted(d, key=elem_key)
        except:
            pass
    else:
        d = list(d)
    for k in d:
        r.append(latex_repr(k, **kwargs))
    return ensuremath(f"\\{{{', '.join(r)}\\}}")


def parens(s, force=False):
    if force or len(s) > 0 and (not s[0] == "(" or not s[-1] == ")"):
        return f"({s})"
    else:
        return s

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


class AttrWrapper:
    """Wrap a mapping so that keys are accessible directly as properties. It
    will also pass a call through to a callable wrapped argument (which may
    or may not be supported)."""
    def __init__(self, m):
        if isinstance(m, AttrWrapper):
            m = m._m
        self._m = m

    def __call__(self, *args, **kwargs):
        """Calls the wrapped object"""
        # currently only Model implements __call__
        return self._m(*args, **kwargs)

    def __getattr__(self, k):
        return self._m[k]


class Namespace(collections.abc.MutableMapping):
    """A mapping implementation with functionality for managing metalanguage
    namespaces. Underlying uses `collections.ChainMap` for implementation, and
    so supports many of the features of that class."""
    def __init__(self, *maps):
        """Given some (possibly empty) sequence of maps, instantiate a
        `Namespace` using those maps chained together. Earlier maps have
        precedence."""

        self.items = collections.ChainMap(*maps)

    def __getitem__(self, key):
        """Return the current value for `key`"""
        return self.items[key]

    def __setitem__(self, key, value):
        """Set a value for `key`"""
        self.items[key] = value

    def __delitem__(self, key):
        """Delete a value for `key`. Like the underlying `collections.ChainMap`,
        this may leave `key` set if deleting the current value reveals another
        in a chained map."""
        del self.items[key]

    def __iter__(self):
        """Iterate over keys"""
        # flatten before providing iterator
        return iter(self.items)

    def __len__(self):
        """Count keys"""
        return len(self.items)

    def copy(self):
        """Return a copy of `self`. Subclasses will need to override.

        Returns
        -------
        Namespace
            The copied `Namespace`.
        """
        return Namespace(*self.items.maps.copy())

    def flatten(self):
        """Return a map that flattens any chained mappings in `self`, losing
        update history. Does not modify `self`.

        Returns
        -------
        Namespace
            The flattened `Namespace`. (Note that in subclasses this will
            return an object whose type is the current class.)
        """
        # inelegant but works with subclasses
        r = self.copy()
        r.items = collections.ChainMap(dict(r.items))
        return r

    def update(self, *args, **kwargs):
        """Update `self` according to any mappings and key values provided,
        affecting only the first map in the chain. This function has the
        same api as `collections.abc.MutableMapping.update`.
        """
        self.items.update(*args, **kwargs)

    def modify(self, m=None, /, **kwargs):
        """Modify `self` by creating a new element in the underlying mapping
        chain, and updating with `m` and `**kwargs`.

        Parameters
        ----------
        m : collections.abc.Mapping, optional
            A mapping to update with
        **kwargs : dict, optional
            Key-value pairs to update with
        """
        self.items = self.items.new_child(m, **kwargs)

    def new_child(self, m=None, /, **kwargs):
        """Return a modified version of `self` (which is unchanged), that has
        had a new mapping added to the chain with optional updates from `m`
        and `**kwargs`.

        Parameters
        ----------
        m : collections.abc.Mapping, optional
            A mapping to update with
        **kwargs : dict, optional
            Key-value pairs to update with

        Returns
        -------
        Namespace
            The modified namespace. (Note that in subclasses this will
            return on object whose type is the current class.)

        See also
        --------
        This is the same api as `collections.ChainMap.new_child`.
        """

        r = self.copy()
        r.modify(m, **kwargs)
        return r

    def pop_child(self):
        """Remove and return the mapping at the head of the chain, modifying
        `self`. Like `collections.ChainMap.parents`, if the chain has only
        one map, this will reset `self` to an empty `Namespace`.

        Returns
        -------
        collections.abc.Mapping
            The popped mapping.
        """
        ret = self.maps[0]
        self.items = self.items.parents
        return ret

    @property
    def parents(self):
        """Return a `Namespace` object that pops the first mapping (if any).
        Does not affect `self`. Like `collections.ChainMap.parents`, if the
        chain has only one map, this will return an empty `Namespace`.

        Returns
        -------
        Namespace
            The parent namespace. (Note that in subclasses this will
            return on object whose type is the current class.)

        See also
        --------
        This is the same api as `collections.ChainMap.parents`.
        """
        # written to work with subclasses
        r = self.copy()
        r.pop_child()
        return r

    def reset(self):
        """Reset `self` to an empty `Namespace`."""
        self.items = collections.ChainMap({})

    @property
    def maps(self):
        """Return the underlying sequence of chained maps.

        See also
        --------
        This is the same api as `collections.ChainMap.parents`.
        """
        return self.items.maps

    @contextlib.contextmanager
    def shift(self, assignment=None, **kwargs):
        """A context manager that, given some updates to the namespace, yields
        a context with the namespace temporarily shifted. (This doesn't cause
        this namespace to take any sort of scope!)

        Yields
        ------
        AttrWrapper
            A wrapped version of `self` with keys exposed as properties
        """
        # in principle we could work with self.items.maps directly, but it
        # seems safer to just save `self.items`, so we can exactly return
        # to the old state. This does rely on `modify` changing self.items.
        old = self.items
        try:
            self.modify(assignment, **kwargs)
            yield AttrWrapper(self)
        finally:
            self.items = old

    @contextlib.contextmanager
    def under(self, target=None):
        """Temporarily apply all definitions in this namespace to the targeted
        namespace (via `shift`), which by default, is the global namespace.
        Modifying the targeted namespace in the scope of this call will change
        this namespace! (This behavior can be avoided by copying first.)

        Parameters
        ----------
        target: Namespace, optional
            A namespace to shift. If `None`, this call will use
            `meta.global_namespace()`.

        Yields
        ------
        AttrWrapper
            A wrapped version of the shifted namespace.
        """

        from .meta import global_namespace
        if target is None:
            target = global_namespace()

        with target.shift(self) as ns:
            # note: changes to the global namespace in the scope of this call
            # will change this namespace! Also, ChainMap is perfectly happy
            # to have multiple refs to identical dicts, so reentering the global
            # namespace is possible, but is effectively inert.
            yield ns

    def text(self, rich=True, **kwargs):
        """Return text for a rich (markdown) or plain repr."""
        if len(self) == 0:
            # subclass cosmetics: use the current class' name for the empty
            # message.
            emsg = f"(Empty {self.__class__.__name__})"
            if rich:
                emsg = f"*{emsg}*"
            return emsg
        from .display import assignment_repr
        lines = [assignment_repr(k, self[k], rich=rich) for k in self]
        if rich:
            join = "<br />\n"
        else:
            join = "\n"
        return join.join(lines)

    def _repr_markdown_(self):
        return self.text(rich=True)

    def __repr__(self):
        # XX may be better as repr_pretty
        return self.text(rich=False)


# a minimal frozendict implementation, to support type domains that need a hashable
# function representation. There's lots of bells and whistles one could add
# here, but at the moment I don't see the need.
# TODO: possibly consider using https://github.com/MagicStack/immutables, since
# it has very efficient copying and seems to be (more or less) maintained.
# Perhaps one day:
class frozendict(collections.abc.Mapping):
    def __init__(self, mapping):
        if isinstance(mapping, frozendict):
            self._store = mapping._store
            self._hash = mapping._hash
        else:
            if not isinstance(mapping, dict):
                # handles the case where mapping is a sequence
                mapping = dict(mapping)
            self._store = mapping
            self._hash = None

    def compute_hash(self):
        # This is *a* hash function, but I really have no idea if it's any good.
        # Uses frozenset's hash to ensure that this is order invariant.
        # note: this requires all values to be hashable types...
        self._hash = hash(frozenset(zip(self._store.keys(), self._store.values())))

    def __eq__(self, other):
        # XX compare to MetaTerms?
        if isinstance(other, frozendict):
            return self._store == other._store
        else:
            return False

    def __hash__(self):
        if self._hash is None:
            self.compute_hash()
        return self._hash

    def __getitem__(self, k):
        return self._store[k]

    def __len__(self):
        return len(self._store)

    def __iter__(self):
        return iter(self._store)

    def __repr__(self):
        return f"frozendict({repr(self._store)})"
