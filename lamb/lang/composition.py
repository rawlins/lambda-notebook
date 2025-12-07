#!/usr/local/bin/python3
import collections, itertools, logging, html, enum, contextlib

from lamb import utils, types, meta, display
from lamb.utils import ensuremath
from lamb.types import type_e, type_t, type_property, TypeMismatch
from lamb.meta import  TypedExpr, true_term, term, is_te
from lamb.meta.core import partial, pbody, pcond
from lamb.meta.meta import Assignment
from lamb import tree_mini

from lamb.meta.core import te, tp
from lamb.parsing import ParseError


try:
    from collections import MutableMapping
except:
    from collections.abc import MutableMapping

Tree = utils.get_tree_class()


# There are three main kinds of things defined in here: Composables,
# CompositionSystems, and CompositionOps.
#
#  * A CompositionSystem describes a set of composition operations, as well as
#    a lexicon.  At the heart of it, this is the object that runs semantic
#    composition.
#
#  * A Composable is any object that can be composed with any other.  There are
#    a variety of types of Composables:
#     - SingletonComposables:  containers that represent a single composable
#       denotation.  Some key subclasses are Composite, Item, and TreeComposite.
#       Item represents a single lexical entry.  The Composite classes
#       (typically) represent some composed denotation, though they are general
#       enough that they don't need to.  (Item inherits from TreeComposite, for
#       example.)
#     - CompositionResult: a container that may represent multiple composed
#       denotations.
#     - CompositionTree: Tracks composition results in the context of a
#       nltk.Tree structure.
#
#  * A CompositionOp is a container class that performs some composition
#    operation on one or more Composables. There are two sorts:
#    TreeCompositionOps work on trees (currently just binary trees) and produce
#    a result form composing the daughter nodes.  BinaryCompositionOp and
#    UnaryCompositionOp are simpler and don't assume any tree structure, but
#    just take Composables.  These two modes of composition aren't meant to be
#    used in the same system.



# TODO: relocate double bracket config to `display`?

# configurable bracketing options. BARS is always safe.
# This is configurable because historically the nicer looking options could be
# slower than the uglier ones, depending on the MathJax render mode. In 2023
# it's a bit over-elaborate..
global bracket_setting
class DoubleBrackets(enum.Enum):
    BARS = 1  # ascii
    FANCY = 2 # unicode/latex
    UNI = 3   # unicode only

bracket_setting = DoubleBrackets.FANCY

from lamb.display import latex_text, latexbf

def inbr_doublebracket_uni(s):
    return f"⟦{s}⟧"

def inbr_doublebar(s):
    return f"||{s}||"

def text_inbr(s):
    """Convenience function to wrap something in double brackets, for
    regular strings."""
    if (bracket_setting == DoubleBrackets.FANCY
                or bracket_setting == DoubleBrackets.UNI):
        return inbr_doublebracket_uni(s)
    else: # BARS
        return inbr_doublebar(s)

def inbr_doublebracket(s, negspace=True):
    if display.latex_mode == display.LatexMode.KATEX:
        # katex on colab appears to support this out of the box! (Though its
        # implementation appears to be essentially the negative spacing trick)
        return f"\\llbracket {{{s}}}\\rrbracket "
    elif negspace:
        # otherwise, we use negative spacing to get the symbols
        # TODO: maybe wrap in {}?
        return f"[\\![{s}]\\!]"
    else:
        # legacy approach, historically the negative spacing trick slowed down
        # rendering quite a bit. This is dead code, as far as display routines
        # are concerned, but leave it in for now. Unicode bracket actually
        # looks pretty good in MathJax output, it just potentially leads to
        # paste issues for the latex source.
        return inbr_doublebracket_uni(s)

def inbr_raw(s):
    """Convenience function to wrap something in double brackets, for MathJax
    output."""
    if bracket_setting == DoubleBrackets.FANCY:
        return inbr_doublebracket(s)
    else:
        return text_inbr(s)

def inbr(s):
    return inbr_raw(latexbf(s))

def latex_super(s, super):
    return f"{s}^{{{super}}}"

def inbrs(s, super):
    """Wrap a string in brackets with a superscript, for MathJax output."""
    return latex_super(inbr(s), super)

# TODO: this is very mislabeled...
def mathjax_indent():
    """Indentation suitable for MathJax output."""
    return "&nbsp;&nbsp;&nbsp;&nbsp;"

def indent(latex=False):
    if latex:
        return mathjax_indent()
    else:
        return "    "

def latex_indent():
    return indent(latex=True)

def set_system(s):
    """Set the (module-level) current composition system."""
    global composition_system
    composition_system = s

def get_system():
    """Get the (module-level) current composition system."""
    global composition_system
    return composition_system

set_system(None)

def compose(*args, **kwargs):
    return get_system().compose(*args, **kwargs)

class CompositionFailure(Exception):
    def __init__(self, *items, reason=None):
        self.reason = reason
        if isinstance(reason, types.TypeMismatch):
            self.items = [reason.i1, reason.i2]
        else:
            self.items = list()
        self.items.extend(items)

    def item_str(self, i, latex=False):
        if latex:
            try:
                return i._repr_latex_()
            except:
                return repr(i)
        else:
            return repr(i)

    def items_str(self, latex=False):
        return " * ".join(
            [self.item_str(i, latex=latex) for i in self.items])

    def class_desc(self, latex=False):
        # TODO: convert to markdown
        if latex:
            return '<span style="color:red"><b>Composition failure</b></span>'
        else:
            return "Composition failure"

    def description(self, latex=False):
        if isinstance(self.reason, types.TypeMismatch):
            # TODO: do something with any extra items?
            return self.reason.description(latex=latex)
        else:
            main_str = self.class_desc(latex=latex)
            return f"{main_str} on: {self.items_str(latex=latex)}  ({self.reason})"

    def latex_str(self, **kwargs):
        return self.description(latex=True)

    def _repr_html_(self):
        return self.description(latex=True)

    def __str__(self):
        return self.description(latex=False)

    def __repr__(self):
        return str(self)

class PreconditionFailure(CompositionFailure):
    def class_desc(self, latex=False):
        # TODO: convert to markdown
        if latex:
            return '<span style="color:red"><b>Composition precondition failure</b></span>'
        else:
            return "Composition precondition failure"

class Composable(object):
    """Abstract mixin for objects that can be composed using a composition
    system; provides * and **.
    """

    def compose(self, other=None, assignment=None):
        cs = get_system()
        if cs is None:
            raise NotImplementedError
        if other is None:
            return cs.compose(self, assignment=assignment)
        else:
            if not (isinstance(other, Composable)):
                raise NotImplementedError
        return cs.compose(self, other, assignment=assignment)

    def placeholder(self):
        return False

    def get_index(self):
        return None

    def get_index_str(self):
        # generalize to other features?
        if self.get_index() is None:
            return ""
        else:
            return "[idx: %d]" % self.get_index()

    def content_iter(self):
        try:
            return iter(self.content)
        except:
            return iter((self.content,))

    def content_len(self):
        return len(list(self.content_iter()))

    @property
    def constant(self):
        return False

    def _repr_html_(self):
        # ... is this needed?
        # (currently: there are some direct calls to _repr_html_() that seem
        # to go through here; these should be cleaned up)
        return self.show()._repr_html_()

    def latex_str(self):
        # ... is this needed? does it even work any more?
        return self.show()._repr_latex_()

    # should return an IPython repr-able object, usually a utils.BaseLNDisplay
    # object of some kind
    def show(self, recurse=True, style=None):
        raise NotImplementedError(repr(self))

    # should return a display.DisplayNode object
    def build_display_tree(self, derivations=False, recurse=True, style=None):
        raise NotImplementedError(repr(self))

    # should return an IPython repr-able object, usually a utils.BaseLNDisplay
    # object of some kind
    def tree(self, derivations=False, recurse=True, style=None):
        return utils.show(
            html=self.build_display_tree(derivations=derivations,
                                            recurse=recurse, style=style))

    def __mul__(self, other):
        return self.compose(other)

    def __pow__(self, other):
        r = self * other
        return r


class AssignmentController(object):
    """This class is for managing the rendering and maintenance of specialized
    variables in the assignment function.

    For example, in many systems, index variables are notated as superscripts
    to the interpretation function.

    See the notebook on adding composition operations for an example.
    """
    def __init__(self, specials=None, reserved=None):
        if specials is None:
            specials = []
        self.specials = specials
        self.reserved = {"index"}
        if reserved is not None:
            self.reserved = self.reserved | set(reserved)

    def validate(self, a):
        # could check key names
        return True

    def render(self, a=None, latex=False, hide_reserved=True):
        if a is None:
            a = self.default()
        out_l = []
        for s in self.specials:
            if s.op in a.keys():
                if s.op in self.reserved and hide_reserved:
                    continue
                if a[s.op].term() and s.op == a[s.op].op:
                    if latex:
                        out_l.append(ensuremath("%s" % (a[s.op].latex_str(suppress_parens=True))))
                    else:
                        out_l.append("%s" % (a[s.op]))
                else:
                    if latex:
                        out_l.append(ensuremath("%s_\\{%s\\} = %s" %
                                (s.op,
                                 a[s.op].type.latex_str(),
                                 a[s.op].latex_str(suppress_parens=True))))
                    else:
                        out_l.append("%s = %s" % (s.op, a[s.op]))
        if isinstance(a, Assignment) and a.name:
            # XX something less dumb here (a - specials?)
            out_l.append(a.name)
        if latex:
            return ensuremath(", ".join(out_l))
        else:
            return "[" + ", ".join(out_l) + "]"

    def default(self):
        a = {x.op: x for x in self.specials}
        return Assignment(a)

class VacuousAssignmentController(object):
    def __init__(self):
        pass

    def validate(self, a):
        return True

    def render(self, a=None, latex=False, hide_reserved=True):
        return ""

    def default(self):
        return Assignment()


# at the moment, this is a fairly cosmetic subclass
class Lexicon(utils.Namespace):
    def __init__(self, items=None):
        if items is None:
            items = {}
        super().__init__(items)

    def copy(self):
        return Lexicon(self.items.copy())


class SingletonComposable(Composable):
    """A SingletonComposable stores one denotation ('content') in some form."""
    def __init__(self, content, system=None):
        if system is None:
            system = get_system()
        self.system = system
        if content is None or isinstance(content, Exception):
            self.content = content
        else:
            self.content = te(content)

    @property
    def type(self):
        if self.content is None or isinstance(self.content, Exception):
            return None
        else:
            return self.content.type

    @property
    def assign_controller(self):
        if self.system is None:
            return VacuousAssignmentController()
        else:
            return self.system.assign_controller

    def under_assignment(self, assignment):
        a = self.assign_controller.default().merge(assignment)
        return self.content.under_assignment(a)

    def composite_name(self, *others):
        return "[" + " ".join([self.name] + [o.name for o in others]) + "]"

    def short_str(self, latex=False, i=None, **args):
        if i is None:
            istr = ""
        else:
            istr = f"[{i}]"
        if latex:
            return ensuremath(inbrs(self.name + istr,
                                    self.assign_controller.render(latex=True))
                              + self.type_str_latex())
        else:
            return f"{text_inbr(self.name + istr)}{self.assign_controller.render(latex=False)}"

    def type_str_latex(self):
        if self.type is None:
            return ""
        else:
            return "_{" + self.type.latex_str() + "}"

    def short_str_latex(self, i=None):
        return self.short_str(latex=True, i=i)
        

    def find_steps(self):
        return self

    def step_tree(self):
        return self

    def text(self, i=None, suppress_parens=True, rich=True):
        if self.content is None:
            # vacuous element
            # XX separate rendering for vacuous indexed elements?
            if rich:
                return ensuremath(self.short_str(latex=True, i=i) + "\\text{ [vacuous]}")
            else:
                return self.short_str(latex=False, i=i) + " *vacuous*"
        elif isinstance(self.content, Exception):
            # error
            # TODO: the relevant exceptions would need markdown to be displayed.
            # they can still be viewed by looking at `content` directly...
            if rich:
                return ensuremath(self.short_str(latex=False, i=i) + "\\:=\\:" + latexbf("error!"))
            else:
                return self.short_str(latex=False, i=i) + " = **error**!"
        elif isinstance(self.content, PlaceholderTerm):
            # placeholder during tree composition
            if rich:
                return self.content.latex_str()
            else:
                return repr(self.content)

        # everything else
        if rich:
            return (ensuremath(self.short_str(latex=True, i=i)
                    + " \\:=\\: "
                    + self.content.latex_str(suppress_parens=suppress_parens)))
        else:
            # XX suppress_parens ignored
            return f"{self.short_str(latex=False, i=i)} = {repr(self.content)}"

    def latex_str(self, i=None, suppress_parens=True):
        return self.text(i=i, suppress_parens=suppress_parens, rich=True)

    def __repr__(self):
        # TODO: make this parse?
        return self.text(rich=False)

    def show(self):
        # is using `latex` generally safe here?
        return utils.show(latex=self.latex_str(), plain=self.text(rich=False))

    def _repr_latex_(self):
        return self.latex_str()

    def _repr_html_(self):
        return None # override superclass (TODO, improve)

    def compose_str_latex(self):
        return self.latex_str()

    def content_iter(self):
        return iter((self,))

    def failed(self):
        return isinstance(self.content, Exception)

class CompositionTree(Tree, Composable):
    """A CompositionTree is the most complex container object for denotations.
    It represents denotations paired with nodes in an nltk.Tree-style
    representation, and inherits from nltk.Tree.  It is intended for tree-style
    composition, not treeless."""

    def __init__(self, node, children=None, denotation=None, system=None):
        if children is None:
            children = list()
        tree_label = node is not None and node or ""
        Tree.__init__(self, tree_label, children=children)
        self.children = self # hack, but _why_ did they have to inherit directly
                             # from list??
        if system is None:
            self.system = get_system()
        else:
            self.system = system
        if denotation is None:
            self.denotations = None
        elif isinstance(denotation, CompositionResult):
            self.denotations = denotation
        elif isinstance(denotation, Composable):
            self.denotations = [denotation,]
        elif isinstance(denotation, TypedExpr):
            raise NotImplementedError() # TODO use an Item?
        else:
            self.denotations = list(denotation) # requires iterable

    @property
    def constant(self):
        """Is the denotation of this node constant or calculated?  If constant,
        it should never be overwritten."""

        # TODO: case where there are multiple denotations and only some are
        # constant?  This might come up for idioms...
        if len(self.denotations) == 1 and self.denotations[0].constant:
            return True
        return False

    def placeholder(self):
        """Is the denotation a placeholder for something not yet composed?"""
        if (self.denotations is not None
                    and len(self.denotations) == 1
                    and self.denotations[0].placeholder()):
            return True
        return False

    def build_placeholder(self, override=True):
        """Inserts or replaces the content of this node with a PlaceholderTerm.
        If override is set, this will overwrite whatever might be here,
        unless that content itself is set to have its "constant" variable be
        True.  For example, a lexical item (Item) will have this set."""

        if self.denotations is None or (override and not self.constant):
            if isinstance(self.label(), str):
                placeholder = TreeComposite(
                    content=PlaceholderTerm(self.label().lower(),
                                            self,
                                            system=self.system),
                    mode="Placeholder", source=self)
                self.denotations = [placeholder,]
            else:
                raise NotImplementedError()

    def source_tree(self):
        """Convert a CompositionTree into a plain Tree object; useful in order
        to display it among other things."""
        # code dup with TreeComposite
        def _as_source_tree(x):
            try:
                return x.source_tree()
            except AttributeError:
                return x
        return Tree(self.name, [_as_source_tree(c) for c in self.children])

    def build_local_tree(self, override=True):
        """This function ensures that any necessary PlaceholderTerms are
        inserted into the denotation of a daughter node."""
        if len(self) == 0:
            self.build_placeholder(override=override)
        else:
            for i in range(len(self)):
                ch = self[i]
                if not isinstance(ch, CompositionTree):
                    if isinstance(ch, str):
                        ch = CompositionTree(ch, system=self.system)
                        self[i] = ch
                    elif isinstance(ch, Composable):
                        ch = CompositionTree.tree_factory(ch,
                                                            system=self.system)
                        self[i] = ch
                    elif isinstance(ch, Tree):
                        ch = self.from_tree(ch, system=self.system)
                        self[i] = ch
                    else:
                        raise NotImplementedError()
                ch.build_placeholder(override)
        return self

    @property
    def content(self):
        return self.denotations

    def content_iter(self):
        return iter(self.denotations)

    def compose(self, other=None, override=True, assignment=None):
        """Calculate the meaning of this node from the meanings (if available)
        of the parts.  If meanings of the parts are unknown, insert a
        placeholder."""
        if other is not None:
            return self.system.compose(self, other, assignment=assignment)
        if override:
            self.old_denotations = self.denotations
            self.denotations = None
        if self.denotations is None:
            self.build_local_tree(override=False) # do not want to override
                                                  # non-placeholder children
            self.percolate_failures()
            if not self.failed():
                self.denotations = self.system.compose_container(self,
                                                        assignment=assignment)
        return self

    def __mul__(self, other):
        return Composable.__mul__(self, other)

    def compose_path(self, path, assignment=None):
        if len(path) > 0:
            sub = self[path[0]]
            if not isinstance(sub, CompositionTree):
                sub = self.tree_factory(sub)
            sub = sub.compose_path(path[1:], assignment=assignment)
            self[path[0]] = sub
            if self.composed():
                # redo any super-nodes that were already composed
                return self.compose(override=True, assignment=assignment)
            else:
                return self
        else:
            return self.compose(override=True, assignment=assignment)

    def composed(self):
        return self.denotations is not None

    def build_composite(self, den): # TODO: use a factory function
        return TreeComposite(*self.children, content=den, source=self)

    def flatten_iter(self):
        # prone to combinatorial explosion?
        if self.content is not None and len(self.content) > 0:
            yield from self.content_iter() # double check -- is source set
                                           # properly?
        else:
            if len(self) == 0:
                yield TreeComposite(content=None, source=self)
            elif len(self) == 1:
                try:
                    iter0 = self[0].flatten_iter()
                except:
                    yield self[0]
                    raise StopIteration()
                for c in iter0:
                    yield TreeComposite(c, content=None, source=self)
            elif len(self) == 2:
                # just some duck punching...
                try:
                    iter0 = self[0].flatten_iter()
                except AttributeError:
                    iter0 = iter([self[0]])
                try:
                    iter1 = self[1].flatten_iter()
                except AttributeError:
                    iter1 = iter([self[1]])
                for c0 in iter0:
                    for c1 in iter1:
                        yield TreeComposite(c0, c1, content=None, source=self)
            else:
                raise NotImplementedError()

    def find_empty_results(self):
        empty = list()
        for c in self:
            if isinstance(c.content, CompositionResult):
                if c.content.empty():
                    empty.append(c.content)
        return empty

    def short_str(self, latex=False, children=True, force_brackets=False,
                                                                        **args):
        if isinstance(self.label(), str):
            n = self.label()
        elif isinstance(self.label(), SingletonComposable):
            n = self.label().short_str(latex=latex)
        else:
            n = str(self.label())
        c_list = []
        if children:
            for c in self.children:
                if isinstance(c, str):
                    c_list.append(c)
                elif isinstance(c, CompositionTree):
                    c_list.append(c.short_str(latex=latex, children=False,
                                                        force_brackets=False))
                elif isinstance(c, Tree):
                    c_list.append(str(c.label()))
                else:
                    c_list.append(str(c))
        if len(c_list) > 0:
            n = "[%s %s]" % (n, " ".join(c_list))
        if force_brackets:
            if latex:
                # TODO: figure out how to get assignment controller to render
                # here?  Right now this is tracked on singleton composables
                # only.
                return ensuremath(inbr(n))
            else:
                return text_inbr(n)
        else:
            return n

    @property
    def name(self):
        return self.short_str(children=False)

    def latex_str(self):
        if self.content is None:
            return Tree._repr_html_(self)
        elif isinstance(self.content, CompositionResult):
            return self.content.latex_str() # TODO more?
        elif len(self.content) == 1:
            return self.content[0].latex_str(suppress_parens=True)
        else:
            raise NotImplementedError()

    @property
    def failures(self):
        if isinstance(self.content, CompositionResult):
            return self.content.failures
        else:
            return None

    def failed(self):
        return (not self.placeholder()
                and self.content is not None
                and self.content.failed())

    def percolate_failures(self):
        child_failures = [c.content for c in self.children if c.failed()]
        if len(child_failures):
            self.denotations = CompositionResult(self, list(), child_failures,
                source=self)

    def tree(self, derivations=False, recurse=True, style=None):
        # TODO: set plain
        return utils.show(
            html=self.build_display_tree(derivations=derivations,
                                        recurse=recurse, style=style))

    def show(self,derivations=False, short=True, failures=False, style=None):
        """Show the step-by-step derivation(s) as a proof tree."""
        if self.content is None:
            return self.tree(derivations=derivations, style=style)
        elif isinstance(self.content, CompositionResult):
            if short:
                return self.content.show(style=style, failures=failures)
            else:
                return self.content.tree(derivations=derivations, style=style)
        elif len(self.content) == 1:
            return self.content[0].tree(derivations=derivations, style=style)
        else:
            raise NotImplementedError()

    def paths(self, derivations=False, style=None):
        return self.show(derivations=derivations, short=False, style=style)

    def build_display_tree(self, derivations=False, recurse=True, style=None):
        defaultstyle = {"border": False}
        style = display.merge_styles(style, defaultstyle)
        parts = list()
        for i in range(len(self)):
            try:
                part_i = self[i].build_display_tree(recurse=recurse,
                                        derivations=derivations, style=style)
            except AttributeError:
                leaf_style = display.leaf_style(style)
                part_i = display.DisplayNode(content=self[i],
                                             style=leaf_style)
            parts.append(part_i)
        if self.composed():
            s = self.content.build_summary_for_tree(style=style)
            leaf_style = display.leaf_style(dict(style, align="center"))
            node_parts = list()
            if leaf_style.get_style(None, "definiendum", True):
                node_parts.append(self.short_str(latex=True,
                                                 children=False,
                                                 force_brackets=True))
            node_parts.append(s)
            node = display.DisplayNode(parts=node_parts, style=leaf_style)
        else:
            try:
                node = self.label()._repr_html_()
            except:
                node = str(self.label())

        node_style = display.deriv_style(style)
        return display.DisplayNode(content=node, parts=parts, style=node_style)

    def _ipython_display_(self):
        import IPython
        IPython.display.display(self.show())

    @classmethod
    def from_tree(cls, t, system=None):
        """Factory method to construct a CompositionTree from an nltk.Tree.

        Note that this doesn't convert the whole tree, just the top node."""
        return CompositionTree(t.label(), t, system=system)

    @classmethod
    def tree_factory(cls, composable, system=None):
        """Try to build a CompositionTree from some source.

        Currently, this mainly takes Composables.

        If it receives a string (or a Tree), it will build a (denotation-less)
        CompositionTree with that string/tree node as the node label. If it
        receives a Composable, it will try to find a way to use that Composable
        as the denotation, and come up with a node label.

        Not yet implemented: TypedExpr
        """
        if system is None:
            system = get_system()
        if isinstance(composable, str):
            t = Tree(composable, children=list())
            return CompositionTree.from_tree(t, system=system)
        if isinstance(composable, meta.TypedExpr):
            raise NotImplementedError()
        elif isinstance(composable, Composable):
            if isinstance(composable, Item) or isinstance(composable, Items):
                if not system.has_item(composable):
                    meta.logger.info(
                        "Adding item to lexicon before composing: "
                        + repr(composable))
                    system.add_item(composable)
                t = Tree(composable.name, children=list())
                return system.compose(t)
            if isinstance(composable, CompositionTree):
                return composable
            elif isinstance(composable, TreeComposite):
                if composable.source is not None:
                    if isinstance(composable.source, CompositionTree):
                        return composable.source # Composite already derives
                                                 # from some composition tree
                    elif isinstance(composable.source, Tree):
                        # I think this shouldn't happen any more?
                        ct = CompositionTree.from_tree(composable.source,
                                                                system=system)
                        ct.denotation = [composable,]
                        return ct
                    else:
                        meta.logger.warning(
                            "Unknown source '%s' when converting a "
                            "TreeComposite to a CompositionTree"
                            % repr(composable.source))
                return CompositionTree(composable.name,
                                       children=composable.children,
                                       denotation=composable,
                                       system=system)
            else:
                try:
                    name = composable.composite_name()
                except Exception:
                    name = composable.name # may still fail?
                return CompositionTree(name,
                                       children=None,
                                       denotation=composable,
                                       system=system)
        elif isinstance(composable, Tree):
            return CompositionTree.from_tree(composable, system=system)
        else:
            raise NotImplementedError()


class Composite(SingletonComposable):
    """Abstract class used mainly for single deterministic composition
    results."""
    def __init__(self, part_structure, content, mode=None, source=None):
        SingletonComposable.__init__(self, content)
        self.part_structure = part_structure
        self.mode = mode
        self.source = source

    @property
    def name(self):
        # TODO: other cases?
        if (self.source is None):
            return str(self.part_structure)
        else:
            if isinstance(self.source, Tree):
                return str(self.source.label())
            else:
                return str(self.source)

class TreeComposite(Composite, Tree):
    """A TreeComposite represents a single denotation that results from
    composition in a tree structure.  It inherits from nltk.Tree as well as
    Composite.

    For multiple denotations or non-determinism, see CompositionTree."""
    def __init__(self, *children, content=None, mode=None, source=None):
        if isinstance(source, Composite) and source.source is not None:
            source = source.source # TODO: recursive?
        if isinstance(content, Composite):
            if mode is None:
                mode = content.mode
            content = content.content

        Composite.__init__(self, children, content, mode=mode, source=source)
        tree_label = content is not None and content or ""
        Tree.__init__(self, tree_label, children)
        self.children = self # hack
        self.collapsed_paths = list()
        self.collapsed_count = 1
        self.inherit_index = None
        for c in children:
            if isinstance(c, TreeComposite):
                self.collapsed_count *= c.collapsed_count

    @property
    def p1(self):
        return self[0]

    @property
    def p2(self):
        return self[1]

    def source_tree(self):
        """Convert a TreeComposite into a plain Tree object; useful in order
        to display it among other things."""
        # code dup with CompositionTree
        def _as_source_tree(x):
            try:
                return x.source_tree()
            except AttributeError:
                return x
        return Tree(self.name, [_as_source_tree(c) for c in self.children])

    def get_index(self):
        return self.inherit_index

    def extend_collapsed_paths(self, tc):
        self.collapsed_paths.append(tc)
        if isinstance(tc, TreeComposite):
            self.collapsed_paths.extend(tc.collapsed_paths)
            self.collapsed_count += tc.collapsed_count

    def collapsed_compose_str(self):
        s = ""
        i = 0
        for p in self.collapsed_paths:
            if p.mode is None:
                continue
            if i > 0:
                s += ", "
            i += 1
            s += p.mode.name
        return s

    def all_paths(self):
        return [self, ] + self.collapsed_paths

    def placeholder(self):
        if self.content is not None and isinstance(self.content,
                                                            PlaceholderTerm):
            return True
        return False

    def compose_str_latex(self):
        return self.compose_str(latex=True)

    def compose_str(self, latex=False, collapsed=True):
        if isinstance(self.content, Exception):
            if latex:
                try:
                    return self.content.latex_str(suppress_parens=True)
                except:
                    return str(self.content)
            else:
                return str(self.content)
        else:
            s = ""
            if latex:
                combination = " * ".join([n.short_str_latex() for n in self])
            else:
                combination = " * ".join([n.short_str() for n in self])
            if len(combination) > 0:
                s += combination + " leads to: "
            if latex:
                s += self.latex_str()
            else:
                s += repr(self)
            if self.mode is not None:
                if latex:
                    s += " <b>[by %s]</b>" % self.mode.name
                else:
                    s += " [by %s]" % self.mode.name
            if collapsed:
                cstr = self.collapsed_compose_str()
                if len(cstr) > 0:
                    s += (" (%i equivalent paths not shown: %s)"
                                        % (len(self.collapsed_paths), cstr))
            return s

    def find_steps(self):
        steps = list()
        for i in range(len(self)):
            if isinstance(self[i], SingletonComposable):
                steps.extend(self[i].find_steps())
        steps.append(self)
        return steps

    def step_tree(self):
        steps = list()
        steps.append(self)
        for i in range(len(self)):
            if isinstance(self[i], SingletonComposable):
                steps.append(self[i].step_tree())
        return steps

    def build_display_tree(self, derivations=False, recurse=True, style=None):
        defaults = {"direction": display.Direction.TD,
                    "border": False,
                    "expl_style": "bracket"}
        style = display.merge_styles(style, defaults)

        leaf_style = display.leaf_style(style)
        int_style = display.internal_style(style)
        node_style = display.deriv_style(style)

        parts = list()
        for i in range(len(self)):
            if not isinstance(self[i], Composable):
                continue
            if isinstance(self[i], str):
                part_i = display.DisplayNode(parts=[self[i]], style=leaf_style)
            else:
                part_i = self[i].build_display_tree(derivations=derivations,
                                                    recurse=recurse,
                                                    style=style)
            parts.append(part_i)
        if self.content is not None:
            content_str = utils.ensuremath(self.content.latex_str(suppress_parens=True))
        elif self.get_index() is not None:
            content_str = self.get_index_str()
        else:
            content_str = "N/A"
        if self.placeholder():
            node_content = display.DisplayNode(parts=[content_str],
                                               style=int_style)
            expl = None
        else:
            if self.mode:
                if isinstance(self.mode, str):
                    expl = self.mode
                else:
                    expl = self.mode.name
                collapsed = self.collapsed_compose_str()
                if len(collapsed) > 0:
                    expl = display.alternative_explanation(expl,
                                                self.collapsed_compose_str())
            else:
                expl = None
            # TODO revisit and generalize this (maybe override Item in a better
            # way?)
            if expl is not None and len(parts) == 0:
                # no subparts but there is an explanation.  This is the case of
                # a leaf node derived from a tree. show the short str in the
                # slot for a part
                parts.append(display.DisplayNode(parts=[self.short_str_latex()],
                                                 style=leaf_style))
                if derivations and self.content.derivation is not None:
                    node_content = self.content.derivation.equality_display(
                                                                        None)
                else:
                    node_content = display.DisplayNode(parts=[content_str],
                                                       style=int_style)
            else:
                if derivations and self.content.derivation is not None:
                    node_content = self.content.derivation.equality_display(
                                                        self.short_str_latex())
                else:
                    # this is the normal case
                    if len(parts) == 0:
                        cur_style = leaf_style # this is a mess
                    else:
                        cur_style = int_style
                    node_parts = list()
                    if cur_style.get_style(None, "definiendum", True):
                        node_parts.append(self.short_str_latex())
                    node_parts.append(content_str)
                    node_content = display.DisplayNode(parts=node_parts,
                                                       style=int_style)
        if expl is None and len(parts) == 0:
            node_content.style = leaf_style
            return node_content # don't add a superfluous containing div
        if len(parts):
            final_style = node_style
        else:
            final_style = leaf_style
        return display.DisplayNode(content=node_content,
                                   explanation=expl,
                                   parts=parts,
                                   style=final_style)

    @property
    def name(self):
        try:
            return self.__node_name__
        except:
            pass
        # TODO: other cases?
        if (self.source is None):
            if len(self) == 2:
                return self.p1.composite_name(self.p2)
            elif len(self) == 1:
                return self.p1.composite_name()
            else:
                return ""
        else:
            if isinstance(self.source, Tree):
                if isinstance(self.source.label(), str):
                    return self.source.label()
                else:
                    return repr(self.source.label())
            else:
                # can generate crashes if this isn't a str...
                return self.source

    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as
        possible."""
        if self.content is not None:
            self.content = self.content.simplify_all(reduce=True)
        return self

    def _repr_latex_(self):
        # since this inherits from Tree, need to ensure that we don't inherit
        # a monkey-patched _repr_latex_ from there.
        return self.latex_str()

class BinaryComposite(TreeComposite):
    def __init__(self, p1, p2, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, p2, content=content, mode=mode,
                                                                source=source)

class UnaryComposite(TreeComposite):
    def __init__(self, p1, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, content=content, mode=mode,
                                                                source=source)

class CompositionResult(Composable):
    """Container class for a stage of a composition.  Can represent multiple
    composition paths, and tracks failures."""

    def __init__(self, items, results, failures, source=None):
        """Construct a CompositionResult given the output of the things that
        can happen while doing composition.

        `items`: a list of Composables that were the input to the
                 CompositionStep.  These might themselves be CompositionResults.
        `results`: a list of results from composition.
        `failures`: a list of failed composition paths, usually in the form of
                    information-rich CompositionFailure objects.
        `source`: some representation of a natural language structure that led
                  to this composition step.

        """
        self.items = items
        self.failures = failures
        self.source = source
        self.result_hash = dict()
        self.results = list()
        for r in results:
            self.add_result(r)

    def __repr__(self):
        return ("CompositionResult(results=%s, failures=%s)"
                                % (repr(self.results), repr(self.failures)))

    def __str__(self):
        return self.summary(plain=True)

    @property
    def name(self):
        try:
            return self.source.name
        except:
            if self.source is None:
                return "Anonymous CompositionResult"
            else:
                return str(self.source)

    def summary(self, recurse=True, style=None, failures=False, plain=False):
        s = ""
        newline = plain and "\n" or "<br />\n"
        if (len(self.results) == 0):
            if self.source is None:
                s += "Composition failed:"
            else:
                s += ("Composition of \"%s\" failed:" % (self.name))
            s += newline + self.failures_str(latex = not plain)
        else:
            if (len(self.results) == 1):
                s += "1 composition path.  Result:"
            else:
                s += "%i composition paths. Results:" % len(self.results)
            n = 0
            for composite in self.results:
                num = composite.collapsed_count
                s += (newline + indent(latex = not plain) + "[%i]: " % n)
                if plain:
                    s += composite.compose_str()
                else:
                    s += composite.latex_str()
                if num > 1:
                    if plain:
                        s += " (%i equivalent paths lead here)" % num
                    else:
                        s += (" &nbsp;&nbsp;<span style=\"font-size:small\">(%i equivalent paths lead here)</span>"
                                % num)
                n += 1
            if failures:
                s += (newline + newline
                        + "Composition attempts that failed:" + newline
                        + self.failures_str(latex = not plain))
        return s

    def source_tree(self):
        trees = [i.source_tree() for i in self]
        # convenient for rendering, possibly very annoying programmatically:
        if len(trees) == 1:
            trees = trees[0]
        return trees

    def show(self, recurse=True, style=None, failures=False):
        # TODO: the plain version of this is extremely unreadable
        return utils.show(markdown=self.summary(plain=False, recurse=recurse, style=style, failures=failures),
            plain=self.summary(plain=True, recurse=recurse, style=style, failures=failures))

    def _ipython_display_(self):
        # note: currently this sidesteps implementing _repr_pretty_ by having
        # the repr returned by show() be different than the object's repr...
        # maybe not ideal?
        import IPython
        IPython.display.display(self.show())

    def build_summary_for_tree(self, style=None):
        defaultstyle = {"align": "left"}
        style = display.merge_styles(style, defaultstyle)
        leaf_style = display.leaf_style(style)
        if self.failed():
            failed_modes = [f.mode.name for f in self.failures if (
                            isinstance(f, Composite)
                            and not isinstance(f.content, PreconditionFailure))]
            if len(failed_modes):
                failed_modes = [display.alert_span("failed: " +
                                                ", ".join(failed_modes))]
            else:
                failed_modes = []
            return display.DisplayNode(
                parts=["Composition Failure!"] + failed_modes,
                style=leaf_style)
        else:
            n = 0
            parts = list()
            for composite in self.results:
                span = display.element_with_text("span",
                    style="color:blue; white-space:nowrap; display:inline-block;",
                    text="[path %i]: " % n)
                parts.append([span, composite.latex_str()])
                n += 1
            return display.DisplayNode(parts=parts, style=leaf_style)

    def failures_str_latex(self):
        return self.failures_str(latex=True)

    def failures_str(self, latex=False, preconditions=False):
        s = str()
        failed_precond = list()
        newline = latex and "<br />\n" or "\n"
        for f in self.failures:
            if isinstance(f, CompositionResult):
                if f.source is None:
                    s += "Inheriting composition failure." + newline
                else:
                    s += ("Inheriting composition failure from \"%s\"." %
                          f.name) + newline
                if latex:
                    s += f.failures_str(latex=latex, preconditions=preconditions)
                else:
                    s += str(f)
            elif isinstance(f, Composite):
                if (not preconditions
                            and isinstance(f.content, PreconditionFailure)):
                    failed_precond.append(f)
                    continue
                if latex:
                    s += latex_indent() + f.content.latex_str(suppress_parens=True)
                else:
                    s += "    " + str(f.content)
                s += newline
            else:
                raise NotImplementedError(f.__class__)
        if len(failed_precond):
            s += (indent(latex=latex)
                  + ("%d operations failed preconditions: %s."
                     % (len(failed_precond),
                        ", ".join([n.mode.name for n in failed_precond]))))
            s += newline
        return s

    def failures_trace_latex(self):
        raise NotImplementedError

    def trace(self, subpaths=False):
        """Trace all derivation paths in detail"""
        return self.full_trace_latex(subpaths=subpaths)

    def full_trace_latex(self, subpaths=False):
        """Trace all derivation paths in detail"""
        s = str()
        i = 1
        s += "Full composition trace.  "
        if len(self.results) == 0:
            s += ("No successful paths -- tracing failures...<br />\n" +
                        self.failures_trace_latex())
            return s
        elif len(self.results) == 1:
            s += "1 path:<br />\n"
        else:
            s += "%i paths:<br />\n" % len(self.results)
        for r in self.results:
            spcount = r.collapsed_count
            if subpaths:
                spaths = r.all_paths()
            else:
                spaths = (r,)
            sub_i = 1
            for path in spaths:
                steps = path.find_steps()
                step_i = 1
                if len(self.results) > 1 or spcount > 1:
                    if spcount > 1:
                        if subpaths:
                            spstr = ".%i" % sub_i
                        else:
                            spstr = (" (%i equivalent sub-paths not shown)"
                                                            % (spcount - 1))
                    else:
                        spstr = ""
                    s += "<b>Path %i%s:</b><br />\n" % (i, spstr)
                for step in steps:
                    if step is path:
                        s += (latex_indent() +
                              ("Step %i: " % step_i) +
                              step.compose_str(latex=True,
                                               collapsed=(not subpaths)) +
                              "<br />\n")
                    else:
                        s += (latex_indent() +
                              ("Step %i: " % step_i) +
                              step.compose_str(latex=True) +
                              "<br />\n")
                    step_i += 1
                sub_i += 1
            i += 1
        # TODO: set plain here
        return utils.show(markdown=s)

    def tree(self, recurse=True, derivations=False, style=None):
        """Show the step-by-step derivation(s) as a proof tree."""
        s = str()
        if len(self.results) == 0:
            return "No succesful composition paths."
        elif len(self.results) == 1:
            s += "1 composition path:<br />"
        else:
            s += "%i composition paths:<br />\n" % len(self.results)
        i = 0
        for r in self.results:
            if len(self.results) > 1 or r.collapsed_count > 1:
                s += "Path [%i]:" % i
                if r.collapsed_count > 1:
                    s += "(%i other equivalent paths)" % (r.collapsed_count - 1)
                s += "<br />\n" 
            # this will return a LNDisplay-packaged string.
            rst = r.tree(derivations=derivations, recurse=recurse, style=style)
            s += rst._repr_html_() + "<br /><br />"
            i += 1
        # TODO: set plain properly here...
        return utils.show(html=s)

    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as
        possible."""

        # this is a bit complicated because reducing in place may change the
        # hash of any results. (not to mention collapse results.) It's generally
        # better to just enable reduction in the composition system.
        rcopy = list(self.results)
        dirty = False
        for r in rcopy:
            if r.content is None:
                continue
            old_c = r.content
            new_c = r.content.simplify_all(reduce=True)
            if new_c != old_c:
                dirty = True
                # TODO probably should copy
                # currently, works by side effect
                r.content = new_c
        if dirty:
            self.results = list()
            self.result_hash = dict()
            for r in rcopy:
                self.add_result(r)
        return self

    def result_items(self):
        return self.results

    def __iter__(self):
        return self.content_iter()

    @property
    def content(self):
        return self.result_items()

    def content_iter(self):
        return iter(self.result_items())

    def empty(self):
        return (len(self.results) == 0)

    def __len__(self):
        return len(self.results)

    def failed(self):
        return len(self.failures) > 0 and self.empty()

    def __getitem__(self, i):
        return self.results[i]

    def add_result(self, r):
        if r.content in self.result_hash:
            self.result_hash[r.content].extend_collapsed_paths(r)
        else:
            self.result_hash[r.content] = r
            self.results.append(r)

    def extend(self, other):
        """Extend this with another Composable."""
        if not isinstance(other, Composable):
            raise ValueError
        for r in other.content_iter():
            self.add_result(r)
        try:
            # not all Composables implement failures
            self.failures.extend(other.failures)
        except AttributeError:
            pass

    def prune(self, i, reason=None):
        """Remove result `i` with some specified `reason`.

        Will move the derivation into the `failures` list."""
        result = Composite(self.results[i],
            CompositionFailure(self.results[i], reason=reason))
        del self.result_hash[self.results[i].content]
        del self.results[i]
        self.failures.append(result)

class CRFilter(object):
    """A filter on CompositionResults that enforces some specified
    meta-language criteria."""

    def __init__(self, name, filter_fun):
        """Construct a filter on CompositionResults.

        `name`: the name of the filter.
        `filter_fun`: a function that implements the filter on a single
                      TypedExpr.

        The simplest case would be e.g. to check that a derivation has a
        specific type."""

        self.filter_fun = filter_fun
        self.name = name

    def __call__(self, cresult):
        #TODO this modifies cresult in place, perhaps should make a copy?
        i = 0
        while i < len(cresult.content):
            passes = self.filter_fun(cresult.content[i].content)
            if passes:
                i += 1
            else:
                cresult.prune(i, reason=self.name)
        return cresult

class Items(CompositionResult):
    def __init__(self, item_list):
        CompositionResult.__init__(self, list(), item_list, list())

    def text(self, rich=True):
        if (len(self.results) == 0):
            return "Empty item list"
        else:
            rows = []
            for i in range(len(self.results)):
                assert self.results[i].collapsed_count == 1
                rows.append(self.results[i].text(i=i, rich=rich))

            if rich:
                join = "\n<br />"
            else:
                join = "\n"
            return join.join(rows)

    def show(self, **kwargs):
        return utils.show(markdown=self.text(rich=True), plain=self.text(rich=False))

    def __repr__(self):
        # XX this would work better as _repr_pretty_
        return self.text(rich=False)

    @property
    def name(self):
        if len(self.results) == 0:
            return ""
        else:
            return self.results[0].name

    def __setitem__(self, i, value):
        if value.content in self.result_hash:
            return
        self.results[i] = value
        self.result_hash[value.content] = value

    def __getitem__(self, i):
        if isinstance(i, slice):
            return Items(self.results[i])
        else:
            return self.results[i]

    def __delitem__(self, i):
        del self.result_hash[self.results[i].content]
        del self.results[i]

    def add_result(self, r):
        # disallow adding duplicates (allowed by CompositionResult)
        if r.content not in self.result_hash:
            CompositionResult.add_result(self, r)

class Item(TreeComposite):
    """This class represents a lexical item.  It is implemented as a
    TreeComposite without a daughter."""

    def __init__(self, nl_name, content, index=None, mode=None):
        """Construct an Item.

        `nl_name`: the natural language name of the Item.
        `content`: a TypedExpr content for the item.
        `index`: the index, if any.  (For traces, etc)
        `mode`: passed to superclass (not currently used).
        """
        TreeComposite.__init__(self, content=content, mode=mode)
        self.__node_name__ = nl_name
        if index is None:
            self.index = None
        else:
            if index > 0:
                self.index = index
            else:
                self.index = 0

    def get_index(self):
        # ugh, there's an annoying namespace pollution here because of
        # nltk.Tree inheriting directly from `list`. Probably this variable
        # should be renamed, but for now just wrap in a method that is also
        # defined in Composable to just return None.
        return self.index

    def __eq__(self, other):
        if isinstance(other, Item):
            return (self.name == other.name
                and self.content == other.content
                and self.index == other.index)
        else:
            return super().__eq__(other)

    @property
    def constant(self):
        return not self.placeholder()

    def copy(self):
        new_content = self.content
        if new_content is not None:
            new_content = new_content.copy()
        return Item(self.name, new_content, index=self.index)

    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as
        possible."""
        if self.content is not None:
            self.content = self.content.simplify_all(reduce=True)
        return self

    def reduce(self):
        if self.content is not None:
            self.content = self.content.reduce()
        return self

    def placeholder(self):
        if isinstance(self.content, PlaceholderTerm):
            return True
        return False

    def interpret(self, assignment):
        if self.index == None:
            return self.content.under_assignment(assignment)
        else:
            a2 = meta.subassignment(assignment, index=index)
            # XX previously this didn't use a2...
            return self.content.under_assignment(a2)

    def build_display_tree(self, derivations=False, recurse=None, style=None):
        defaultstyle = {}
        style = display.merge_styles(style, defaultstyle)
        leaf_style = display.leaf_style(style)
        if not self.content:
            desc = self.get_index() is None and "N/A" or self.get_index_str()
            return display.DisplayNode(parts=[self.short_str_latex(),
                                              desc],
                                              style=leaf_style)
        else:
            return super().build_display_tree(derivations=derivations,
                                              recurse=recurse,
                                              style=style)

class CompositionOp(object):
    """A unary composition operation."""
    def __init__(self, name, operation, composite_name=None,
                                        allow_none=False,
                                        reduce=False,
                                        system=None,
                                        source=None):
        """Build a composition operation given some function.  See also
        `unary_factory`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take
                     Composable(s) and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from
                          the operands.
        `allow_none`: can the argument to `operation` have content None?
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be
                  set/changed automatically if this operation is added to a
                  system.)
        `source`: if set, an object (can be a function or a metalanguage object)
                  that provides some information about how the composition
                  operation was built. Used for jupyter-style reprs.
        """
        self.operation = operation
        self.__name__ = name
        self.allow_none = allow_none
        if composite_name is not None:
            self.composite_name = composite_name
        if system is not None:
            self.system = system
        self.reduce = reduce # shadows builtin
        self.source = source
        self.set_descriptions_from_source(source)

    def set_descriptions_from_source(self, source):
        if source is None:
            source = self.operation
        if isinstance(source, meta.TypedExpr):
            self.desc = "combinator '%s'" % repr(TypedExpr)
            self.latex_desc = "combinator '%s'" % source._repr_latex_()
        elif callable(source):
            import types
            if isinstance(source, types.FunctionType):
                self.desc = "python function '%s.%s'" % (source.__module__,
                                                         source.__name__)
                self.latex_desc = self.desc
            else:
                self.desc = "python object '%s' of %s" % (source.__name__,
                                                          source.__class__)
                # __class__ tends to have <> in it
                self.latex_desc = html.escape(self.desc)
        else:
            self.desc = repr(source)
            self.latex_desc = repr(source)


    def _repr_html_(self):
        if self.latex_desc is None:
            return ("%s <i>%s</i>, built on python function '%s.%s'" %
                        (self.description(),
                         self.name,
                         self.operation.__module__,
                         self.operation.__name__))
        else:
            return ("%s <i>%s</i>, built on %s" %
                        (self.description(),
                         self.name,
                         self.latex_desc))

    def __repr__(self):
        if self.desc is None:
            return ("%s %s, built on python function '%s.%s'" %
                        (self.description(),
                         self.name,
                         self.operation.__module__,
                         self.operation.__name__))
        else:
            return ("%s %s, built on %s" %
                        (self.description(),
                         self.name,
                         self.desc))

    @property
    def name(self):
        return self.__name__

    @property
    def arity(self):
        raise NotImplementedError

    def composite_name(self, i1):
        raise NotImplementedError

    def __call__(self, *a, assignment=None):
        # handle None here, rather than in all individual functions.
        raise NotImplementedError

    def description(self):
        return self.__class__.__name__


class BinaryCompositionOp(CompositionOp):
    """A composition operation on two Composables."""
    def __init__(self, name, operation, commutative=False,
                                        allow_none=False,
                                        reduce=True,
                                        system=None,
                                        source=None):
        """Build a composition operation given some function.  See also
        `binary_factory` and `binary_factory_curried`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take two
                     Composables and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `allow_none`: can either of the arguments to `operation` have content
                      None?  (See e.g. the PA rule.)
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be
                  set/changed automatically if this operation is added to a
                  system.)
        `source`: if set, an object (can be a function or a metalanguage object)
                  that provides some information about how the composition
                  operation was built. Used for jupyter-style reprs.
        """
        super().__init__(name, operation, allow_none=allow_none,
                                          reduce=reduce,
                                          system=system,
                                          source=source)
        self.commutative = commutative
        self.typeshift = False

    @property
    def arity(self):
        return 2

    def composite_name(self, i1, i2):
        return "[%s %s]" % (i1.name, i2.name)

    def __call__(self, i1, i2, assignment=None):
        # handle None here, rather than in all individual functions.
        if (not self.allow_none) and (i1.content is None or i2.content is None):
            raise CompositionFailure(i1, i2, reason="%s disallows None"
                                                                % self.name)
        result = self.operation(i1, i2, assignment=assignment)
        result.mode = self
        if self.reduce:
            result = result.reduce_all()
        return result

    def description(self):
        return "Binary composition rule"

class UnaryCompositionOp(CompositionOp):
    """A unary composition operation."""
    def __init__(self, name, operation, typeshift=False,
                                        composite_name=None,
                                        allow_none=False,
                                        reduce=True,
                                        system=None,
                                        source=None):
        """Build a composition operation given some function. See also
        `unary_factory`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take one
                     Composable and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from
                          the operands.
        `allow_none`: can the argument to `operation` have content None?
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be
                  set/changed automatically if this operation is added to a
                  system.)
        """
        super().__init__(name, operation, composite_name=composite_name,
                                          allow_none=allow_none,
                                          reduce=reduce,
                                          system=system,
                                          source=source)
        self.typeshift = typeshift

    @property
    def arity(self):
        return 1

    def composite_name(self, i1):
        return "[%s]" % (i1.name)

    def __call__(self, i1, assignment=None):
        # handle None here, rather than in all individual functions.
        if (not self.allow_none) and (i1.content is None):
            raise CompositionFailure(i1, reason="%s disallows None" % self.name)
        result = self.operation(i1, assignment=assignment)
        result.mode = self
        if self.reduce:
            result = result.reduce_all()
        return result

    def description(self):
        if self.typeshift:
            return "Typeshift"
        else:
            return "Unary composition rule"

def tree_binary(t):
    """Returns true just in case `t` is locally binary branching."""
    return (len(t) == 2)

def tree_unary(t):
    """Returns true just in case `t` is locally unary branching."""
    return (len(t) == 1)

def tree_leaf(t):
    """Returns true just in case `t` is a leaf node."""
    return (len(t) == 0)


class TreeCompositionOp(object):
    """A composition operation on a local tree segment."""
    def __init__(self, name, operation, preconditions=None,
                                        commutative=False,
                                        allow_none=False,
                                        reduce=True,
                                        system=None,
                                        source=None):
        """Build a composition operation on trees given some function.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation. Must take a tree
                     structure and an optional assignment.
        `preconditions`: a function that checks some preconditions on a tree
                         structure, returning a boolean.  Defaults to checking
                         binarity.
        `commutative`: should the operation be tried in both orders?  NOTE:
                       currently not used.
        `allow_none`: can some node have content None?
        `system`: the composition system that this is part of.  (Will be
                  set/changed automatically if this operation is added to a
                  system.)
        """
        self.operation = operation
        self.__name__ = name
        self.commutative = commutative
        self.allow_none = allow_none
        if preconditions is None:
            self.preconditions = tree_binary
        else:
            self.preconditions = preconditions

        # adding the rule to a system will set this, no need to pre-check
        self.system = system
        self.reduce = reduce
        self.typeshift = False
        self.set_descriptions_from_source(source)

    def set_descriptions_from_source(self, source):
        if source is None:
            source = self.operation
        if isinstance(source, meta.TypedExpr):
            self.desc = "combinator '%s'" % repr(TypedExpr)
            self.latex_desc = "combinator '%s'" % source._repr_latex_()
        elif callable(source):
            import types
            if isinstance(source, types.FunctionType):
                self.desc = "python function '%s.%s'" % (source.__module__,
                                                         source.__name__)
                self.latex_desc = self.desc
            else:
                self.desc = "python object '%s' of %s" % (source.__name__,
                                                          source.__class__)
                # __class__ tends to have <> in it
                self.latex_desc = html.escape(self.desc)
        else:
            self.desc = repr(source)
            self.latex_desc = repr(source)


    def _repr_html_(self):
        if self.latex_desc is None:
            return ("%s <i>%s</i>, built on python function '%s.%s'" %
                        (self.description(),
                         self.name,
                         self.operation.__module__,
                         self.operation.__name__))
        else:
            return ("%s <i>%s</i>, built on %s" %
                        (self.description(),
                         self.name,
                         self.latex_desc))

    def __repr__(self):
        if self.desc is None:
            return ("%s %s, built on python function '%s.%s'" %
                        (self.description(),
                         self.name,
                         self.operation.__module__,
                         self.operation.__name__))
        else:
            return ("%s %s, built on %s" %
                        (self.description(),
                         self.name,
                         self.desc))

    @property
    def name(self):
        return self.__name__

    @property
    def arity(self):
        return 1

    def description(self):
        if self.preconditions == tree_binary:
            return "Binary tree composition rule"
        elif self.preconditions == tree_unary:
            return "Unary tree composition rule"
        else:
            return "Tree composition rule"

    def composite_name(self, t):
        return t.label()

    def __str__(self):
        return "Tree composition op '%s'" % self.name

    # this could be a classmethod, as it doesn't reference anything on an
    # instance.  Old version did reference the composition system, however,
    # and this may need to be revisited.  (See CompositionTree.build_local_tree)
    def build_local(self, tree):
        """Convert an arbitrary Tree into a local tree where all children are
        Composables.

        Uses PlaceholderTerm for subtrees which are not yet composed.

        This function is idempotent."""
        if not isinstance(tree, CompositionTree):
            tree = CompositionTree.tree_factory(tree)
        tree.build_local_tree(override=False)
        return tree

    def __call__(self, tree, assignment=None):
        if not self.preconditions(tree):
            #return None
            raise PreconditionFailure(tree,
                            reason="Failed preconditions for %s" % self.name)
        if (not self.allow_none):
            for d in tree:
                if d.content is None:
                    raise CompositionFailure(*tree.children,
                                reason="%s disallows None" % self.name) 
        result = self.operation(tree, assignment=assignment)
        if self.reduce:
            result = result.reduce_all()
        result.mode = self
        return result


class LexiconOp(TreeCompositionOp):
    """A composition operation that looks up a lexical entry in the composition
    system's lexicon."""
    def __init__(self, system=None):
        TreeCompositionOp.__init__(self, "Lexicon", self.lookup,
                                    preconditions=tree_leaf,
                                    system=system,
                                    source=None)

    def freshen(self, tree, c):
        # This accomplishes two things: first, it doesn't include the raw
        # Item in the tree (since this can lead to `mode` getting set on the
        # Item in the lexicon), and second, it ensures that `mode` is set
        # correctly when the lookup is non-deterministic. This latter part
        # may need to be generalized if other composition ops have baked-in
        # non-determinism.
        contents = list(c.content_iter())
        def freshen_composite(tc):
            if isinstance(tc, Item):
                return tc.copy()
            # this other case isn't currently used
            return tc
        fresh = [freshen_composite(r) for r in contents]
        # len 0 case should be impossible at this point...
        if len(fresh) == 1:
            return fresh[0]
        else:
            return CompositionResult(tree, fresh, list(), source=tree)

    def lookup(self, t, assignment=None):
        # TODO: revisit
        if isinstance(t, str):
            name = t
        elif (isinstance(t, TreeComposite)
                            and t.label() is None and t.source is not None):
            name = t.source.label()
        elif (t.label() is not None
                            and isinstance(t.label(), PlaceholderTerm)
                            and t.source is not None):
            name = t.source.label()
        else:
            name = t.label()
        den = self.system.lookup_item(name)
        if den is None:
            raise CompositionFailure(t,
                            reason="No lexical entry for '%s' found." % name)
        return self.freshen(t, den)

    def description(self):
        return "Lexicon lookup"

    def _repr_html_(self):
        return "Lexicon lookup"

    def __repr__(self):
        return "Lexicon lookup"

def unary_factory(meta_fun, name, typeshift=False, reduce=True):
    """Factory function to construct a unary composition operation given some
    function.

    This is extremely useful for building unary operations and type-shifts from
    meta-language combinators.
    """
    def op_fun(arg, assignment=None):
        result = meta_fun(arg.content.under_assignment(assignment))
        return UnaryComposite(arg, result)
    return UnaryCompositionOp(name, op_fun, typeshift=typeshift,
                                            reduce=reduce,
                                            source=meta_fun)

def binary_factory_uncurried(meta_fun, name, reduce=True,
                                                    combinator_source=None,
                                                    commutative=False):
    """Factory function to construct a binary composition operation given some
    function."""
    def op_fun(arg1, arg2, assignment=None):
        result = meta_fun(arg1.content.under_assignment(assignment),
                          arg2.content.under_assignment(assignment))
        return BinaryComposite(arg1, arg2, result)
    if combinator_source is None:
        source = meta_fun
    else:
        source = combinator_source
    return BinaryCompositionOp(name, op_fun, reduce=reduce, source=source, commutative=commutative)

def binary_factory(meta_fun, name, reduce=True, commutative=False):
    """Factory function to construct a binary composition operation given some
    (curried) function.

    This is extremely useful for building operations from meta-language
    combinators.  For example, PM can be implemented using just:
    >lang.binary_factory_curried(lang.pm_op, "PM")
    """
    def op_fun(arg1, arg2, assignment=None):
        result = meta_fun(arg1.content.under_assignment(assignment))(
                                    arg2.content.under_assignment(assignment))
        return BinaryComposite(arg1, arg2, result)
    r = BinaryCompositionOp(name, op_fun, commutative=commutative,
                                          reduce=reduce,
                                          source=meta_fun)
    return r


class PlaceholderTerm(meta.TypedTerm):
    """This class represents a placeholder for some denotation that is unknown
    or not yet composed.  The primary use is in incrementally doing top-down
    composition."""
    def __init__(self, varname, placeholder_for, system=None, **kwargs):
        meta.TypedTerm.__init__(self, varname, types.VariableType.any(),
                                validate_name=False, **kwargs)
        self._variable = False
        self._constant = True
        self.let = True
        self.placeholder_for = placeholder_for
        if system is None:
            self.system = get_system()
        else:
            self.system = system

    @property
    def assign_controller(self):
        return self.system.assign_controller

    def placeholder_name(self):
        """the content of the placeholder is either a string, or a nltk Tree,
        in which case the name is taken from its 'node' field.
        """
        if isinstance(self.placeholder_for, str):
            return self.placeholder_for
        else:
            return self.placeholder_for.label()


    def latex_str(self, **kwargs):
        return ensuremath(inbrs(self.placeholder_name(),
            self.assign_controller.render(latex=True))
            + "_{" + self.type.latex_str() + "}")

    def __repr__(self):
        # TODO: make this parse?
        return (text_inbr(self.placeholder_name())
                    + self.assign_controller.render(latex=False))

    def expand(self):
        """Attempt to expand the node by composing whatever `self` is a
        placeholder for.

        If this composition is already done, just return the result.  (E.g.
        this is memoized.)"""
        if isinstance(self.placeholder_for, str):
            raise NotImplementedError
        else:
            try:
                den = self.placeholder_for.composition_result
            except AttributeError:
                den = self.system.compose(self.placeholder_for)
                self.placeholder_for.composition_result = den
            return den

    def apply(self, arg):
        # use __call__ instead of true application
        return self(arg)

    def copy(self):
        return self.copy_local()

    def copy_local(self, **kwargs):
        result = PlaceholderTerm(self.op, self.placeholder_for,
                                    system=self.system, **kwargs)
        result.let = self.let
        result.type = self.type # type may have changed, e.g. via alphabetic
                                # conversion to a fresh type
        return result

class CompositionSystem(object):
    """A CompositionSystem describes an overarching way of dealing with
    semantic composition, made up of composition rules/operations, types, and a
    lexicon."""
    def __init__(self, rules=None, name=None, a_controller=None):
        self.rules = list()
        self.ruledict = dict()
        for r in rules:
            self.add_rule(r)

        self.name = name

        if a_controller is None:
            self.assign_controller = VacuousAssignmentController()
        else:
            self.assign_controller = a_controller
        self.typecache = set()
        self.lexicon = Lexicon()
        self.update_typeshifts()
        self.typeshift_depth = 3
        self.typeshift = False
        self.view_stack = None

    def copy(self):
        """Make a copy of the composition system."""
        new_sys = CompositionSystem(rules=self.rules,
                                    name=(self.name + " (copy)"),
                                    a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon.copy()
        return new_sys

    @contextlib.contextmanager
    def under_model(self, model):
        with model.under():
            yield

    def assume_model(self, model):
        if self.view_stack is None:
            self.view_stack = contextlib.ExitStack()
        self.view_stack.enter(model.under())

    def reset_assumptions(self):
        # XX what if this is called during model.under() -- should probably
        # error?
        if self.view_stack is not None:
            self.view_stack.close()
            self.view_stack = None

    def add_rule(self, r):
        """Add a composition rule.  `r` should be a CompositionOp of some
        kind."""
        r.system = self
        if r.name is not None:
            if r.name in self.ruledict.keys():
                meta.logger.warning(
                    "Composition rule named '%s' already present in system, "
                    "replacing" % r.name)
                self.rules = [r2 for r2 in self.rules if r2.name != r.name]
            self.ruledict[r.name] = r
        self.rules.append(r)
        self.update_typeshifts()

    def add_unary_rule(self, combinator, name, reduce=True):
        rule = unary_factory(combinator, name, reduce=reduce)
        self.add_rule(rule)
        return rule

    def add_binary_rule(self, combinator, name, reduce=True, commutative=False):
        rule = binary_factory(combinator, name, reduce=reduce,
                                                        commutative=commutative)
        self.add_rule(rule)
        return rule

    def add_binary_rule_uncurried(self, fun, name, reduce=True,
                                                        combinator_source=None,
                                                        commutative=False):
        rule = binary_factory_uncurried(fun, name, reduce=reduce,
                                        combinator_source=combinator_source,
                                        commutative=commutative)
        self.add_rule(rule)
        return rule

    def add_typeshift(self, combinator, name, reduce=True):
        rule = unary_factory(combinator, name, typeshift=True, reduce=reduce)
        self.add_rule(rule)
        return rule

    def remove_rule(self, r):
        """Remove a composition rule by name."""
        if isinstance(r, str):
            name = r
        else:
            name = r.name
        if name not in self.ruledict.keys():
            meta.logger.warning("Composition rule '%s' not found in system"
                                % name)
            return
        del self.ruledict[name]
        self.rules = [r for r in self.rules if r.name != name]
        self.update_typeshifts()

    def get_rule(self, r):
        """return a composition rule by name.  Note that some properties are
        cached, in particular typeshifting.

        In general it may be safest to re-add a rule after modifying it."""
        if isinstance(r, str):
            name = r
        else:
            name = r.name
        return self.ruledict[name]

    # TODO: function for checking if system supports an arbitrary type

    def add_basic_type(self, t):
        ts = meta.get_type_system()
        ts.add_atomic(t)

    def __repr__(self):
        if self.name is None:
            return "Anonymous composition system"
        else:
            return "Composition system: " + self.name

    def __str__(self):
        return self.description(latex=False)

    def description(self, latex=False):
        if self.name is None:
            name = "Anonymous composition system"
        else:
            name = self.name
        s = "Composition system '%s'" % name
        if latex:
            s += "<br />"
        else:
            s += "\n"
        s += "Operations: {"
        if latex:
            s += "<br />"
            for x in self.rules:
                s += "&nbsp;&nbsp;&nbsp;&nbsp;" + x._repr_html_() + "<br />"
            s += "}"
        else:
            s += ", ".join([x.name for x in self.rules]) + "}"
        return s

    def _repr_html_(self):
        return utils.show(self.description(latex=True))._repr_html_()

    def lookup(self, *items):
        """Look up a sequence of potential lexical items, replacing any that
        have one with their lexical entry."""
        r = list()
        for i in items:
            try:
                # this is to catch the case where i is unhashable...couldn't
                # find a better way of doing it.  Comes up because of Tree.
                if i in self.lexicon:
                    r.append(self.lexicon[i])
                else:
                    r.append(i)
            except TypeError:
                r.append(i)
        return r

    def has_item(self, i):
        if isinstance(i, Item) or isinstance(i, Items):
            return self.lookup_item(i.name) == i
        else:
            return i in self.lexicon

    def lookup_item(self, i):
        """Look up a single lexical item `i`.  Currently, `i` should be a
        string."""
        try:
            if i in self.lexicon:
                return self.lexicon[i]
            else:
                return None
        except TypeError:
            return None

    def add_item(self, i):
        """Add a lexical item `i`, where `i` should be an Item."""
        self.lexicon[i.name] = i

    def add_items(self, *items):
        """Add a sequence of lexical items."""
        for i in items:
            self.add_item(i)

    def update_typeshifts(self):
        """Recache the typeshifts.  Called automatically when adding one."""
        typeshifts = list()
        for r in self.rules:
            try:
                if r.typeshift:
                    typeshifts.append(r)
            except AttributeError:
                pass
        self.typeshifts = typeshifts

    def compose(self, *items, assignment=None, block_typeshift=False):
        """Compose the items according to the system.  Each item may be a
        container object."""
        return self.compose_iterables(*items, assignment=assignment,
                                                block_typeshift=block_typeshift)

    def do_typeshifts(self, item, depth=1, include_base=True, assignment=None):
        """Given some Composable `item`, try type-shifting it.

        `item`: a Composable to manipulate.
        `depth`: a max depth to search.  (Defaults to 1.  Loops are possible.)
        `include_base`: should the resulting list include the starting `item`?
        `assignment`: an optional assignment to pass to composition operations.

        Returns a composition result containing any type-shifted denotations,
        plus the base `item` depending on `include_base`.
        """
        l = list([item])
        new_l = list()
        for d in range(0, depth):
            new_l = list()
            for i in l:
                for mode in self.typeshifts:
                    try:
                        result = mode(i, assignment=assignment)
                        new_l.append(result)
                    except TypeMismatch as e:
                        #TODO: record this?
                        continue
                    except CompositionFailure as e:
                        continue
            l = new_l
        l = new_l
        if include_base:
            l.append(item)
        return CompositionResult([item], l, list(), source=item)


    def compose_raw(self, *items, assignment=None, block_typeshift=False):
        """Attempts to compose the provided items.  This is the 'raw' version
        not intended to be called directly, and assumes that non-determinism
        is already taken care of.

        Brute force tries every composition rule and order of items.  Note that
        currently this not handle arities > 2.
        """
        #items = self.lookup(*items)
        ret = CompositionResult(items, list(), list())
        arity = len(items)
        for mode in self.rules:
            if arity != mode.arity:
                #TODO: put something in failure list?
                continue
            if arity == 1:
                if mode.typeshift:
                    continue
                orders = ((0,),)
            elif arity == 2:
                if mode.commutative:
                    orders = ((0, 1),)
                else:
                    orders = ((0, 1), (1, 0))
            else:
                raise NotImplementedError
            for order in orders:
                order_items = (items[i] for i in order)
                try:
                    result = mode(*order_items, assignment=assignment)
                    if len(order) > 1 and order[0] > order[1]:
                        result.reverse()
                    ret.extend(result)
                except (CompositionFailure,
                        TypeMismatch,
                        ParseError) as e:
                    if isinstance(e, ParseError):
                        if e.e and isinstance(e.e, TypeMismatch):
                            # extract TypeMismatches that lead to ParseErrors
                            # somewhere in the composition operation. This is
                            # coming up when building combinators using te
                            e = e.e
                        else:
                            raise e
                    if arity == 1:
                        ret.failures.append(Composite(items[0], e, mode=mode))
                    else:
                        ret.failures.append(BinaryComposite(items[0], items[1],
                                                            e, mode=mode))
        # typeshift as a last resort
        if len(ret.results) == 0 and self.typeshift and not block_typeshift:
            shift_result = self.last_resort_shift(*items, assignment=assignment)
            if shift_result is not None:
                ret.extend(shift_result)
        return ret

    def composite_name(self, *items):
        return "[" + " ".join([i.name for i in items]) + "]"

    def source_from_list(self, *items):
        if len(items) == 0:
            return None
        else:
            return self.composite_name(*items)

    def last_resort_shift(self, *items, assignment=None):
        """Do last-resort style typeshifting (up to a constant depth).  That is,
        while (non-type-shifting) composition fails, try typeshifting deeper
        and deeper until finding some things that compose succesfully.

        The depth is determined by `self.typeshift_depth`.  Depending on the
        shifts, setting this high may result in exponential blowup.

        `items`: the Composable(s) that would be passed to a CompositionOp.
        `assignment`: an optional assignment to pass to composition operations.

        Returns a composition result or None."""
        for i in range(1, self.typeshift_depth):
            new_items = list(items)
            typeshifts_changed = False
            for n in range(len(new_items)):
                new_i_n = self.do_typeshifts(new_items[n], depth=i,
                                                        assignment=assignment)
                new_items[n] = new_i_n
                if len(new_i_n.results) > 1:
                    typeshifts_changed = True
            if typeshifts_changed:
                result = self.compose(*new_items, assignment=assignment,
                                                  block_typeshift=True)
                if len(result.results) > 0:
                    return result
        return None

    def compose_iterables(self, *l, assignment=None, block_typeshift=False):
        failures = list()
        for i in l:
            if i.failed():
                failures.append(i)
        if len(failures):
            return CompositionResult(l, list(), failures,
                                        source=self.source_from_list(*l))

        iters = [x.content_iter() for x in l]
        result = self.compose_iterators(*iters, assignment=assignment,
                                            block_typeshift=block_typeshift)
        result.source = self.source_from_list(*l)
        return result

    def compose_iterators(self, *iters, assignment=None, block_typeshift=False):
        r = CompositionResult(None, [],[]) # does not set source
        # brute force: try every combination in the cartesian product of all
        # iterators.
        for seq in itertools.product(*iters):
            r.extend(self.compose_raw(*seq, assignment=assignment,
                                            block_typeshift=block_typeshift))
        return r

    def compose_container(self, c, assignment=None, block_typeshift=False):
        """Compose a container `c`.  Intended for use with a CompositionTree."""
        r = self.compose_iterators(c.flatten_iter(), assignment=assignment,
                                                block_typeshift=block_typeshift)
        if r.empty() and len(r.failures) == 0:
            # find any errors inherited from subtrees.
            r.failures.extend(c.find_empty_results())
        r.source = c
        return r

class TreeCompositionSystem(CompositionSystem):
    """A composition system for doing composition in tree structures."""
    def __init__(self, rules=None, name=None, a_controller=None):
        CompositionSystem.__init__(self, rules=rules, name=name, a_controller=a_controller)
        if not ("Lexicon" in self.ruledict):
            self.add_rule(LexiconOp(system=self))

    def copy(self):
        new_sys = TreeCompositionSystem(rules=self.rules,
                                        name=self.name,
                                        a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon.copy()
        return new_sys

    # Notes on how composition expansion should work in tree structures
    #
    # expansion use cases:
    # 1. fully automated.
    #    When handed a tree, produce a complete-as-possible CompositionResult
    #    for the whole tree.
    #
    # 2. programmatic stepwise expansion.
    #    For interaction at CLI or ipython notebook.  Given a tree that is
    #    partly or not at all composed, expand the tree one node at a time.
    #     * Support any order of nodes.
    #     * Provide default orders, so that an "expand_next" function is
    #       feasible.  Need: top down bf / df, bottom up.
    #
    # 3. point and click.
    #    long term goal: javascript interface for clicking on a node in a tree
    #    and expanding in place.  (what to do about ambiguities?)
    #
    # Crucial issue for 2,3: relationship of source tree with CompositionResult.

    def td_df_lr_gen(self, tree, parent, path_from_par, len_fun, full_path=None):
        """A generator function that expands a tree in depth-first left-to-right
        order.  See `search_for_unexpanded` for a use-case.

        Not really intended to be called directly.

        `tree`: the tree to expand.
        `parent`: the immediate parent of the tree, if any.
        `path_from_par`: the index of this node relative to the parent, if any.
        `len_fun`: a function that provides a length operation on a tree node.
        `full_path`: the path from the starting point in the tree, if any.  Call
                         with `None` initially (used in recursion).

        yields a 4-tuple, consisting of a tree node, the parent (if any), the
        immediate path from the parent, if any, and the full path from the top
        of the tree.
        """
        # TODO: rethink this
        if full_path is None:
            full_path = tuple()
        yield (tree, parent, path_from_par, full_path)
        if len_fun(tree) == 0:
            raise StopIteration()
        elif len_fun(tree) >= 1:
            for i in range(len_fun(tree)):
                yield from self.td_df_lr_gen(tree[i], tree, i, len_fun,
                                                    full_path=full_path + (i,))

    def bu_df_lr_gen(self, tree, parent, path_from_par, len_fun,
                                                            full_path=None):
        if full_path is None:
            full_path = tuple()
        if len_fun(tree) == 0:
            yield (tree, parent, path_from_par, full_path)
        elif len_fun(tree) >= 1:
            for i in range(len_fun(tree)):
                yield from self.bu_df_lr_gen(tree[i], tree, i, len_fun,
                                                    full_path=full_path + (i,))
            yield (tree, parent, path_from_par, full_path)

    def tree_factory(self, composable):
        if composable is None:
            return None
        return CompositionTree.tree_factory(composable, system=self)

    def simple_composite_name(self, *nodes):
        return "[" + " ".join(nodes) + "]"

    def nary_tree_factory(self, *composables, unary_extend=False):
        trees = [self.tree_factory(c) for c in composables]
        trees = [t for t in trees if t is not None]
        if len(trees) == 1 and not unary_extend:
            return trees[0]
        label = self.simple_composite_name(*[t.label() for t in trees])
        return CompositionTree(label, children=trees, system=self)

    def compose(self, *composables, override=True, assignment=None,
                                                    unary_extend=False):
        tree = self.nary_tree_factory(*composables, unary_extend=unary_extend)
        return tree.compose(assignment=assignment, override=override)

    def unary_extend(self, c, override=True, assignment=None):
        return self.compose(c, override=override, assignment=assignment,
            unary_extend=True)

    def search_for_unexpanded(self, tree, search_gen, expanded_fun, len_fun):
        gen = search_gen(tree, None, None, len_fun)
        for (n, p, path, full_path) in gen:
            if not expanded_fun(n):
                return (n, p, path, full_path)
        return (None, None, None, tuple())

    def is_expanded(self, node):
        #TODO: rethink this
        # note: careful of order of checks here, some superclass relationships
        if isinstance(node, CompositionTree):
            if node.content is None:
                return False
            elif node.placeholder():
                return False
            else:
                return True
        elif isinstance(node, Tree):
            return False
        elif isinstance(node, str):
            return False
        else:
            print(node.__class__)
            raise NotImplementedError

    def len_fun(self, node):
        if isinstance(node, Tree):
            return len(node)
        elif isinstance(node, CompositionResult):
            return len(node)
        elif isinstance(node, Item):
            return 0
        elif isinstance(node, str):
            return 0
        raise NotImplementedError()

    def qsfu(self, tree, order=None):
        """Convenience wrapper around expansion functions.  Uses top-down
        left-to-right expansion order to find a node that has not been expanded.
        (stands for 'quick search for unexpanded')"""
        if order is None:
            order = self.bu_df_lr_gen
        return self.search_for_unexpanded(tree, order, self.is_expanded,
                                                                self.len_fun)

    def compose_path(self, root, path, assignment=None):
        return root.compose_path(path, assignment=assignment)

    def expand_next(self, tree):
        """Convenience wrapper around expansion functions.  Expands whatever
        `qsfu` finds in tree."""
        tree = self.tree_factory(tree)
        (subtree, parent, path_from_parent, full_path) = self.qsfu(tree)
        if subtree is None:
            return None
        return tree.compose_path(full_path)

    def expand_all(self, tree):
        """Expand everything in the tree that can be expanded."""
        # TODO: less of a hack
        cur = self.tree_factory(tree)
        last = None
        while True:
            (subtree, parent, path_from_parent, full_path) = self.qsfu(cur)
            if subtree is None:
                return cur
            if subtree is last:
                return cur
            cur = cur.compose_path(full_path)
            last = subtree

    def add_unary_rule(self, f, name):
        self.add_rule(self.unary_factory(f, name))

    def add_binary_rule(self, f, name, mirror=False, swap=False, uncurried=False):
        if uncurried:
            # note unmirrored arg ordering
            f = (lambda f: lambda x: lambda y: f(x,y))(f)
        if mirror:
            self.add_rule(self.binary_factory(f, f"{name}/left"))
            self.add_rule(self.binary_factory(f, f"{name}/right", swap=True))
        else:
            self.add_rule(self.binary_factory(f, name, swap=swap))

    def add_binary_rule_uncurried(self, f, name, mirror=False):
        return self.add_binary_rule(f, name, mirror=mirror, uncurried=True)

    def add_typeshift(self, combinator, name):
        raise NotImplementedError

    @classmethod
    def unary_factory(cls, f, name):
        def wrapped_combinator(t, assignment=None):
            result = f(t[0].content.under_assignment(assignment))
            return UnaryComposite(t[0], content=result, source=t)
        return TreeCompositionOp(name,
            wrapped_combinator,
            preconditions=tree_unary,
            source=f,
            reduce=True)

    @classmethod
    def binary_factory(cls, f, name, swap=False):
        def wrapped_combinator(t, assignment=None):
            if swap:
                l, r = t[1], t[0]
            else:
                l, r = t
            result = f(
                l.content.under_assignment(assignment))(r.content.under_assignment(assignment))
            return BinaryComposite(l, r, content=result, source=t)
        return TreeCompositionOp(name,
            wrapped_combinator,
            preconditions=tree_binary,
            source=f,
            reduce=True)

# TODO: refactor tree composition to use factory calls
def tree_fa_fun_abstract(f, a, assignment=None):
    """Do function application in a fixed function, argument order."""
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(f, a):
        return None
    result = (f.content.under_assignment(assignment))(
                                        a.content.under_assignment(assignment))
    return result

def tree_left_fa_fun(t, assignment=None):
    """Given some tree node `t`, do FA assuming the left branch is the
    function."""
    result = tree_fa_fun_abstract(t[0], t[1], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/left")
    return BinaryComposite(t[0], t[1], result, source=t)

def tree_right_fa_fun(t, assignment=None):
    """Given some tree node `t`, do FA assuming the right branch is the
    function."""
    result = tree_fa_fun_abstract(t[1], t[0], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/right")
    return BinaryComposite(t[0], t[1], result, source=t)

def tree_nn_fun(t, assignment=None):
    return UnaryComposite(t[0],
                content=t[0].content.under_assignment(assignment), source=t)

def tree_binder_check(t):
    return t.content is None and t.get_index() is not None

def tree_index_carrier(t):
    return len(t) == 1 and tree_binder_check(t[0])

# TODO: some more robust feature system? This shouldn't really be a semantic
# operation.
def tree_percolate_index(t, assignment=None):
    if not tree_index_carrier(t): # also set as precondition
        raise TypeMismatch(t, error="Cannot percolate an index") # abuse of TypeMismatch
    r = UnaryComposite(t[0], content=None, source=t)
    r.inherit_index = t[0].get_index()
    return r

# TODO: refactor so that a TreeCompositionOp is defined here
def binary_trivial(t):
    return (len(t) == 2
        and (t[0].content is None or t[1].content is None)
        and not tree_binder_check(t[0])
        and not tree_binder_check(t[1]))

def tree_binary_vacuous(t, assignment=None, pass_source=True):
    """Handle 'vacuous' children with content None. If both are vacuous, the
    parent content is still None. If exactly one is vacuous, the parent content
    is the other's content. Ignores order."""
    if not binary_trivial(t): # also precondition
        raise TypeMismatch(t[0], t[1], error="Vacuous composition needs at least one fully vacuous element") # abuse of TypeMismatch
    # hacky, needs to be generalized somehow. The issue is that only tree
    # composition expects to pass a source right now, and it needs to be a real
    # tree object, not a list-like.
    source = pass_source and t or None
    if t[0].content is None and t[1].content is None:
        return BinaryComposite(t[0], t[1], content=None, source=source)
    elif t[0].content is None:
        return BinaryComposite(t[0], t[1],
                    content=t[1].under_assignment(assignment), source=source)
    else: #if t[1].content is None:
        return BinaryComposite(t[0], t[1],
                    content=t[0].under_assignment(assignment), source=source)

def binary_vacuous(t1, t2, assignment=None):
    return tree_binary_vacuous([t1, t2], assignment=assignment, pass_source=False)

# combinator for predicate modification
pm_op = te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")

def tree_pm_fun(t, assignment=None):
    """H&K predicate modification -- restricted to type <et>.

    This implementation uses the combinator `pm_op` to perform PM via function
    application.
    """
    ts = meta.get_type_system()
    if not (ts.eq_check(t[0].type, type_property) and 
            ts.eq_check(t[1].type, type_property)):
        raise TypeMismatch(t[0], t[1], "Predicate Modification")

    c1 = t[0].content.under_assignment(assignment)
    c2 = t[1].content.under_assignment(assignment)
    result = ((pm_op(c1))(c2)).reduce_all()
    return BinaryComposite(t[0], t[1], result, source=t)

_pa_reason = "Predicate Abstraction requires a valid binder"

def tree_pa_metalanguage_fun(t, assignment=None):
    """H&K-style Predicate Abstraction, implemented in the metalanguage.

    This shifts the assignment for the interpretation of the sister of the
    binder to match up traces with the bound variable. It assumes the binder is
    the left sister, and will generate a CompositionFailure otherwise."""

    if not tree_binder_check(t[0]):
        raise CompositionFailure(t[0], t[1], reason=_pa_reason)
    vname = f"var{t[0].get_index()}"
    var = term(t[1].content.find_safe_variable(), types.type_e)
    new_a = Assignment(assignment)
    new_a.update({vname: var})
    f = meta.LFun(var, t[1].content.under_assignment(new_a))
    return BinaryComposite(t[0], t[1], f, source=t)

def tree_pa_sbc_fun(t, assignment=None):
    """SBC-style Predicate Abstraction, implemented in the metalanguage.

    This shifts the assignment for the interpretation of the sister of the
    binder to match up traces with the bound variable. It assumes the binder is
    the left sister, and will generate a CompositionFailure otherwise."""
    if not tree_binder_check(t[0]):
        raise CompositionFailure(t[0], t[1], reason=_pa_reason)

    var = term(f"var{t[0].get_index()}", types.type_e)
    f = meta.LFun(var, t[1].content.under_assignment(assignment))
    return BinaryComposite(t[0], t[1], f, source=t)

class IndexedPronoun(Item):
    def __init__(self, name, index, typ=None):
        if typ is None:
            typ = types.type_e
        # Item constructor will set self.index
        if index > 0:
            term_name = "var" + str(index)
        else:
            term_name = name
        Item.__init__(self, name, meta.TypedTerm(term_name, typ), index=index)
        
    @property
    def name(self):
        return self.namefun(latex=False)
        
    def namefun(self, latex=False):
        if self.index > 0:
            if latex:
                return latexbf(self.__node_name__) + "_{" + str(self.index) +"}"
            else:
                return self.__node_name__ + str(self.index)
        else:
            return self.__node_name__
        
    def short_str(self, latex=False, i=None, **kwargs):
        name_str = self.namefun(latex=latex)
        # XX why does this have Items code in it
        if i is None:
            istr = ""
        else:
            istr = "[%i]" % i
        if latex:
            return ensuremath(latex_super(inbr_raw(
                                            self.namefun(latex=True) + istr),
                                self.assign_controller.render(latex=True))
                        + self.type_str_latex())
        else:
            return text_inbr(self.namefun(latex=False) + istr)

    @classmethod
    def index_factory(cls, name, typ=None):
        def from_index(index):
            return IndexedPronoun(name, index, typ=typ)
        return from_index
        
class Trace(IndexedPronoun):
    def __init__(self, index, typ=None):
        super().__init__("t", index=index, typ=typ)

    @classmethod
    def index_factory(cls, typ=None):
        def from_index(index):
            return Trace(index, typ=typ)
        return from_index

class Binder(Item):
    """An indexed binder.  Note that its content is always `None`.  Currently
    untyped; this may change."""
    def __init__(self, index, name=None):
        if name is None:
            # fully abstract binder
            name = "%i" % index
        else:
            # TODO: latex rendering
            name = name + str(index)
        Item.__init__(self, name, None, index=index)

class PresupPronoun(IndexedPronoun):
    def __init__(self, name, condition, index, typ=None):
        super().__init__(name, index, typ=typ)
        var = self.content
        self.content = meta.Partial(var, condition(var).reduce_all())
        
    @classmethod
    def index_factory(cls, name, condition, typ=None):
        def from_index(index):
            return PresupPronoun(name, condition, index, typ=typ)
        return from_index

def pa_fun(binder, content, assignment=None):
    """Do predicate abstraction given a `binder` and `content`.

    This is a direct implementation.  Will find a (completely) unused variable
    name to abstract over, and replace any traces of the appropriate index with
    that variable.  This assumes a meta-language implementation of traces!"""
    if not tree_binder_check(binder):
        raise CompositionFailure(binder, content, reason=_pa_reason)

    # there could be more natural ways to do this...should H&K assignment
    # functions be implemented directly?
    name = f"var{binder.get_index()}"
    if name in content.content.get_type_env().terms():
        var_type = content.content.get_type_env().term_type(name)
    else:
        var_type = type_e
    inner_var = term(f"var{binder.get_index()}", var_type)
    inner_fun = meta.LFun(inner_var,
                        content.content.under_assignment(assignment))
    # XX this code is old and messy -- is this convoluted double var thing
    # really needed?
    outer_var = term(inner_fun.find_safe_variable(), var_type)
    f = meta.LFun(outer_var, (inner_fun)(outer_var).reduce())
    return BinaryComposite(binder, content, f)

# TODO: this is the same as tree_fa_fun_abstract, basically...
def fa_fun(fun, arg, assignment=None):
    """Do function application, given some function and argument."""
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(fun, arg):
        raise TypeMismatch(fun, arg, "Function Application needs a matching function and argument")
    return BinaryComposite(fun, arg, 
                (fun.content.under_assignment(assignment)(
                        arg.content.under_assignment(assignment))).reduce())

def pm_fun(fun1, fun2, assignment=None):
    """H&K predicate modification, given two functions.  Restricted to type
    <e,t>.

    This is implemented using the combinator `lang.pm_op`."""
    ts = meta.get_type_system()
    if not (ts.eq_check(fun1.type, type_property) and 
            ts.eq_check(fun2.type, type_property)):
        # this isn't strictly necessary, but will make errors look nicer.
        raise TypeMismatch(fun1, fun2, "Predicate Modification needs property types")
    try:
        varname = fun1.content.varname
    except AttributeError:
        varname = "x"
    c1 = fun1.content.under_assignment(assignment)
    c2 = fun2.content.under_assignment(assignment)
    result = ((pm_op(c1))(c2)).reduce_all()
    return BinaryComposite(fun1, fun2, result)

def presup_fa(f, a):
    f = f.calculate_partiality()
    a = a.calculate_partiality()
    return partial(
        pbody(f)(pbody(a)),
        pcond(a),
        pcond(f)).simplify_all(reduce=True, calc_partiality=True)

def presup_pm(p1, p2):
    p1 = p1.calculate_partiality()
    p2 = p2.calculate_partiality()
    return partial(
        pm_op(pbody(p1))(pbody(p2)),
        pcond(p1),
        pcond(p2)).simplify_all(reduce=True, calc_partiality=True)

def presup_pa(binder, content, assignment=None):
    if not tree_binder_check(binder):
        raise CompositionFailure(binder, content, reason=_pa_reason)
    new_a = Assignment(assignment)
    bound_var = meta.term(f"var{binder.get_index()}", types.type_e)
    outer_var = term(content.content.find_safe_variable(), types.type_e)
    new_a.update({bound_var.op: outer_var})
    # TODO: the bound var here doesn't generally work.
    f = meta.LFun(outer_var,
        content.content.calculate_partiality({bound_var}).under_assignment(new_a))
    return BinaryComposite(binder, content, f)

# this is a presuppositional PA based on the Coppock and Champollion PA rule
def sbc_pa(binder, content, assignment=None):
    if not tree_binder_check(binder):
        raise CompositionFailure(binder, content, reason=_pa_reason)
    bound_var = meta.term(f"var{binder.get_index()}", types.type_e)
    f = meta.LFun(bound_var, content.content.calculate_partiality({bound_var}))
    return BinaryComposite(binder, content, f)


def setup_type_driven():
    """Build a basic bottom-up composition system with PM, FA, and PA.

    The composition system is set to `lang.td_system`.  It's recommended that
    you copy this rather than modifying it directly.  This  is the default
    composition system.

    Also exports a few basic lexical entries for testing purposes."""
    global td_system
    # note that PM is only commutative if the underlying logic has commutative
    # conjunction...
    oldlevel = meta.logger.level
    meta.logger.setLevel(logging.WARNING)
    pm = BinaryCompositionOp("PM", pm_fun, commutative=True)
    fa = BinaryCompositionOp("FA", fa_fun)
    pa = BinaryCompositionOp("PA", pa_fun, allow_none=True)
    vac = BinaryCompositionOp("VAC", binary_vacuous, allow_none=True, commutative=True)
    td_system = CompositionSystem(rules=[fa, pm, pa, vac], name="Type-driven composition")
    set_system(td_system)
    meta.logger.setLevel(oldlevel)

setup_type_driven()

def setup_hk():
    """Build a basic tree composition system modeled after the core system of
    the Heim and Kratzer text. This is not a fully faithful implementation of
    Heim & Kratzer!

    The composition system is set to `lang.hk_system`.  It's recommended that
    you copy this rather than modifying it directly.

    Note that the lexical items defined by `setup_type_driven` can be used here
    too, and are in fact added to the lexicon of this system by default."""
    global hk3_system, hk_system

    tfa_l = TreeCompositionOp("FA/left", tree_left_fa_fun)
    tfa_r = TreeCompositionOp("FA/right", tree_right_fa_fun)
    tpm = TreeCompositionOp("PM", tree_pm_fun)
    tpa = TreeCompositionOp("PA", tree_pa_sbc_fun, allow_none=True)
    nn = TreeCompositionOp("NN", tree_nn_fun, preconditions=tree_unary)
    idx = TreeCompositionOp("IDX", tree_percolate_index,
        preconditions=tree_index_carrier, allow_none=True)
    vac = TreeCompositionOp("VAC", tree_binary_vacuous,
        preconditions=binary_trivial, allow_none=True)

    hk_system = TreeCompositionSystem(rules=[tfa_l, tfa_r, tpm, tpa, nn, idx, vac],
                                       name="H&K Tree-based composition")
    hk3_system = hk_system # backwards compatibility

setup_hk()

def setup_td_presup():
    global td_presup
    td_presup = CompositionSystem(rules=[],
                                  name="Type-driven with partiality")
    td_presup.add_binary_rule_uncurried(presup_fa, "FA")
    pm = td_presup.add_binary_rule_uncurried(presup_pm, "PM")
    pm.commutative = True
    td_presup.add_rule(BinaryCompositionOp("PA", presup_pa, allow_none=True))

setup_td_presup()
