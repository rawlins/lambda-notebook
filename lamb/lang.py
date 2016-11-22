#!/usr/local/bin/python3
import collections, itertools, logging

from lamb import utils, types, meta, display
from lamb.utils import *
from lamb.types import type_e, type_t, type_property, TypeMismatch
from lamb.meta import  TypedExpr, ensuremath, MiniLatex
from lamb import tree_mini
Tree = utils.get_tree_class()


# There are three main kinds of things defined in here: Composables, CompositionSystems, and CompositionOps.
#  * A CompositionSystem describes a set of composition operations, as well as a lexicon.  At the heart of it, this is the object
#    that runs semantic composition.
#  * A Composable is any object that can be composed with any other.  There are a variety of types of Composables.
#     - SingletonComposables:  containers that represent a single composable denotation.  Some key 
#       ones are Composite, Item, and TreeComposite.  Item represents a single lexical entry.  The Composite classes (typically)
#       represent some composed denotation, though they are general enough that they don't need to.  (Item inherits from 
#       TreeComposite for example.)
#     - CompositionResult: a container that may represent multiple composed denotations.
#     - CompositionTree: Tracks composition results in the context of a nltk.Tree structure.
#
#  * a CompositionOp is a container class that performs some composition operation on one or more Composables.
#    There are two sorts: TreeCompositionOps work on trees (currently just binary trees) and produce a result form composing the
#    daughter nodes.  BinaryCompositionOp and UnaryCompositionOp are simpler and don't assume any tree structure, but just take
#    Composables.  These two modes of composition aren't meant to be used in the same system.



# configurable bracketing options.  BRACKET_BARS is always safe.
# This is configurable because the nicer looking options are _much_ slower than the uglier ones, depending on the MathJax render mode.
# for best results, I recommend firefox, with MathJax in SVG mode, and BRACKET_FANCY.
global bracket_setting, BRACKET_BARS, BRACKET_FANCY, BRACKET_UNI
BRACKET_BARS = 1
BRACKET_FANCY = 2
BRACKET_UNI = 3
#bracket_setting = BRACKET_BARS
bracket_setting = BRACKET_FANCY


def text_inbr(s):
    """Convenience function to wrap something in double brackets, for strings."""
    if bracket_setting == BRACKET_BARS:
        return "||" + s + "||"
    elif bracket_setting == BRACKET_FANCY or bracket_setting == BRACKET_UNI:
        return "⟦" + s + "⟧"
    else:
        return "||" + s + "||"

def inbr_doublebracket_uni(s):
    return "⟦\\mathbf{\\text{" + s + "}}⟧"

def inbr_doublebar(s):
    return "||\\mathbf{\\text{" + s + "}}||"

def inbr_doublebracket(s, negspace=False):
    if negspace:
        return "[\![\\mathbf{\\text{" + s + "}}]\!]"
    else:
        return "[[\\mathbf{\\text{" + s + "}}]]"

def inbr(s):
    """Convenience function to wrap something in double brackets, for MathJax output."""
    if bracket_setting == BRACKET_BARS:
        return inbr_doublebar(s)
    elif bracket_setting == BRACKET_FANCY:
        return inbr_doublebracket(s, True)
    elif bracket_setting == BRACKET_UNI:
        return inbr_doublebracket_uni(s)
    else:
        return inbr_doublebar(s)

def inbrs(s, super):
    """Wrap a string in brackets with a superscript, for MathJax output."""
    return inbr(s) + "^{" + super + "}"

def mathjax_indent():
    """Indentation suitable for MathJax output."""
    return "&nbsp;&nbsp;&nbsp;&nbsp;"

latex_indent = mathjax_indent

def set_system(s):
    """Set the (module-level) current composition system."""
    global composition_system
    composition_system = s

def get_system():
    """Get the (module-level) current composition system."""
    global composition_system
    return composition_system

set_system(None)

class Composable(object):
    """Abstract mixin for objects that can be composed using a composition system; provides * and **.
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

    def content_iter(self):
        try:
            return iter(self.content)
        except:
            return iter((self.content,))

    @property
    def constant(self):
        return False

    def _repr_html_(self):
        return self.show()._repr_html_()

    def latex_str(self):
        return self.show()._repr_latex_()

    def show(self, recurse=True, style=None):
        raise NotImplementedError(repr(self))

    def build_display_tree(self, derivations=False, recurse=True, style=None):
        raise NotImplementedError(repr(self))

    def tree(self, derivations=False, recurse=True, style=None):
        return self.build_display_tree(derivations=derivations, recurse=recurse, style=style)
        #return self.latex_step_tree(derivations)

    def latex_step_tree(self, derivations=False):
        """Show the step-by-step derivation(s) as a proof tree."""
        #return meta.MiniLatex(self.latex_step_tree_r(derivations=derivations))
        return self.tree(derivations=derivations)

    def latex_step_tree_r(self, derivations=False):
        raise NotImplementedError(repr(self))

    def __mul__(self, other):
        return self.compose(other)

    def __pow__(self, other):
        r = self * other
        return r

class Assignment(collections.MutableMapping):
    """This class represents an assignment function that can be incrementally modified.  It uses a dict as its store."""
    def __init__(self, base=None, name=None):
        self.store = dict()
        if base is None:
            self.base = Assignment(base=dict())
        else:
            self.base = base
        if name is None:
            self.name = "g"
        else:
            self.name = name

    def __getitem__(self, key):
        if key in self.store:
            return self.store[key]
        else:
            return self.base[key]

    def __setitem__(self, key, value):
        self.store[key] = value

    def __delitem__(self, key):
        # TODO: is this the right behavior?
        del self.store[key]

    def __iter__(self):
        # flatten before providing iterator
        tmp = dict(self.store)
        tmp.update(self.base)
        return iter(tmp)

    def __len__(self):
        return len(self.store) + len(self.base)

    def modify(self, updates):
        new_a = Assignment(self)
        new_a.update(updates)
        return new_a

    def merge(self, assignment):
        """Merge in another assignment.

        This has non-symmetric behavior: if the types are ok, and the value here is a term, 
        the value in `assignment` (at the principal type) will override the value here."""
        new_a = Assignment(self)
        for k in assignment:
            if k in new_a:
                # this will raise a TypeMismatch if the merge fails.
                new_a[k] = meta.merge_tes(new_a[k], assignment[k], symmetric=False)
            else:
                new_a[k] = assignment[k]

    def text(self):
        if isinstance(self.base, Assignment):
            return "%s[%s]" % (self.base.text(), ",".join([("%s/%s" % (self.store[k], k)) for k in self.store.keys()]))
        else:
            return self.name

    def __repr__(self):
        return self.text()

    def __str__(self):
        return repr(self)

    def _repr_latex_(self):
        return self.latex_str()

    def latex_str(self):
        # the superscripting is the Heim & Kratzer style, but I'm not sure I really like it...
        if isinstance(self.base, Assignment):
            return ensuremath("{%s}^{%s}" % (self.base.latex_str(), ",".join([("%s/%s" % (self.store[k], k)) for k in self.store.keys()])))
        else:
            return self.name # TODO: display defaults??


class AssignmentController(object):
    """This class is for managing the rendering and maintenance of specialized variables in the assignment function.

    For example, in many systems, index variables are notated as superscripts to the interpretation function.

    See the notebook on adding composition operations for an example.
    """
    def __init__(self, specials=[], reserved=None):
        self.specials = list(specials)
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
                        out_l.append(ensuremath("%s" % (a[s.op].latex_str())))
                    else:
                        out_l.append("%s" % (a[s.op]))
                else:
                    if latex:
                        out_l.append(ensuremath("%s_\{%s\} = %s" % (s.op, a[s.op].type.latex_str(), a[s.op].latex_str())))
                    else:
                        out_l.append("%s = %s" % (s.op, a[s.op]))
        if isinstance(a, Assignment):
            if latex:
                out_l.append(a.latex_str())
            else:
                out_l.append(repr(a))
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

# TODO: this is not complete
class Lexicon(object):
    def __init__(self):
        self.items = dict()


class SingletonComposable(Composable):
    """A SingletonComposable stores one denotation ('content') in some form."""
    def __init__(self, content, system=None):
        if system is None:
            system = get_system()
        self.system = system
        if content is None or isinstance(content, Exception):
            self.content = content
        else:
            self.content = TypedExpr.ensure_typed_expr(content)

    @property
    def type(self):
        if self.content is None:
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
        a = self.assign_controller.default()
        a.merge(assignment)
        return self.content.under_assignment(a)

    def composite_name(self, other=None):
        if other is not None:
            return "[%s %s]" % (self.name, other.name)
        else:
            return "[%s]" % self.name

    def __repr__(self):
        # TODO: make this parse?
        return text_inbr(self.name) + "%s = %s" % (self.assign_controller.render(latex=False), repr(self.content))

    def short_str(self, latex=False):
        if latex:
            return ensuremath(inbrs(self.name, self.assign_controller.render(latex=True)) + self.type_str_latex())
        else:
            return text_inbr(self.name)

    def type_str_latex(self):
        if self.type is None:
            return ""
        else:
            return "_{" + self.type.latex_str() + "}"

    def short_str_latex(self):
        return self.short_str(latex=True)
        

    def find_steps(self):
        return self

    def step_tree(self):
        return self

    def latex_str(self):
        if self.content is None:
            return ensuremath(self.short_str_latex())
        elif isinstance(self.content, PlaceholderTerm):
            return self.content.latex_str()
        return ensuremath(inbrs(self.name, self.assign_controller.render(latex=True)) + self.type_str_latex() + " \\:=\\: ") + self.content.latex_str()

    def compose_str_latex(self):
        return self.latex_str()

    def content_iter(self):
        return iter((self,))


class CompositionTree(Tree, Composable):
    """A CompositionTree is the most complex container object for denotations.  It represents denotations paired with
    nodes in an nltk.Tree-style representation, and inherits from nltk.Tree.  It is intended for tree-style composition, not
    treeless."""
    def __init__(self, node, children=None, denotation=None, system=None):
        if children is None:
            children = list()
        Tree.__init__(self, node, children=children)
        self.children = self # hack, but _why_ did they have to inherit directly from list??
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
        """Is the denotation of this node constant or calculated?  If constant, it should never be overwritten."""
        # TODO: case where there are multiple denotations and only some are constant?  This might come up for idioms...
        if len(self.denotations) == 1 and self.denotations[0].constant:
            return True
        return False

    def placeholder(self):
        """Is the denotation a placeholder for something not yet composed?"""
        if len(self.denotations) == 1 and self.denotations[0].placeholder():
            return True
        return False

    def build_placeholder(self, override=True):
        """Inserts or replaces the content of this node with a PlaceholderTerm.  If override is set, this will overwrite whatever might be here,
        unless that content itself is set to have its "constant" variable be True.  For example, a lexical item (Item) will have this set."""
        if self.denotations is None or (override and not self.constant):
            if isinstance(self.label(), str):
                placeholder = TreeComposite(content=PlaceholderTerm(self.label().lower(), self ,system=self.system), mode="Placeholder", source=self)
                self.denotations = [placeholder,]
            else:
                raise NotImplementedError()


    def build_local_tree(self, override=True):
        """This function ensures that any necessary PlaceholderTerms are inserted into the denotation of a daughter node."""
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
                        ch = CompositionTree.tree_factory(ch, system=self.system)
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

    def compose(self, override=True, assignment=None):
        """Calculate the meaning of this node from the meanings (if available) of the parts.  If meanings of the parts are
        unknown, insert a placeholder."""
        if override:
            self.old_denotations = self.denotations
            self.denotations = None
        if self.denotations is None:
            self.build_local_tree(override=False) # do not want to override non-placeholder children
            self.denotations = self.system.compose_container(self, assignment=assignment)
        return self

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

    def build_perspective(self, *children):
        ## this is really wrong -- not deleting yet in case I'm missing something
        if isinstance(self.content, CompositionResult):
            return TreeComposite(*children, content=self.content, source=self)
        else:
            if self.content is None or len(self.content) == 0:
                return TreeComposite(*children, content=None, source=self)
            elif len(self.content) == 1:
                return TreeComposite(*children, content=self.content[0], source=self)
            else:
                raise NotImplementedError()

    def perspective_iter(self, *children):
        ## this is really wrong -- not deleting yet in case I'm missing something
        if isinstance(self.content, CompositionResult):
            for c in self.content:
                yield TreeComposite(*children, content=c, source=self)
            raise StopIteration()
        else:
            if self.content is None or len(self.content) == 0:
                # TODO: is this right?
                yield TreeComposite(*children, content=None, source=self)
                raise StopIteration()
            elif len(self.content) == 1:
                yield TreeComposite(*children, content=self.content[0], source=self)
                raise StopIteration()
            else:
                raise NotImplementedError()

    def locally_flat_iter(self): # TODO: generalize to n-ary trees
        """Generator function that yields TreeComposites for every possible denotation of the current node."""
        ## this is really wrong -- not deleting yet in case I'm missing something
        if len(self) == 0:
            yield from self.perspective_iter()
            raise StopIteration()
        elif len(self) == 1:
            if not isinstance(self[0], Composable):
                raise NotImplementedError("Cannot construct an iterator on non-Composables.  (Did compose_container get called without build_local_tree?)")
            for c in self[0].content_iter():
                yield from self.perspective_iter(self[0].build_composite(c))
            raise StopIteration()
        elif len(self) == 2:
            if not isinstance(self[0], Composable) or not isinstance(self[1], Composable):
                raise NotImplementedError("Cannot construct an iterator on non-Composables.  (Did compose_container get called without build_local_tree?)")
            for a in self[0].content_iter():
                for b in self[1].content_iter():
                    yield from self.perspective_iter(self[0].build_composite(a), self[1].build_composite(b))
            raise StopIteration()
        else:
            raise NotImplementedError()

    def flatten_iter(self):
        # prone to combinatorial explosion?
        if self.content and len(self.content) > 0:
            yield from self.content_iter() # double check -- is source set properly?
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

    def short_str(self, latex=False, children=True, force_brackets=False):
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
                    c_list.append(c.short_str(latex=latex, children=False, force_brackets=False))
                elif isinstance(c, Tree):
                    c_list.append(str(c.label()))
                else:
                    c_list.append(str(c))
        if len(c_list) == 0:
            n = "[%s]" % n
        else:
            n = "[%s %s]" % (n, " ".join(c_list))
        if force_brackets:
            if latex:
                # TODO: figure out how to get assignment controller to render here?  Right now this is tracked
                # on singleton composables only.
                return ensuremath(inbr(n))
            else:
                return text_inbr(n)
        else:
            return n

    def latex_str(self):
        if self.content is None:
            return Tree._repr_html_(self)
        elif isinstance(self.content, CompositionResult):
            return self.content.latex_str() # TODO more?
        elif len(self.content) == 1:
            return self.content[0].latex_str()
        else:
            raise NotImplementedError()

    @property
    def failures(self):
        if isinstance(self.content, CompositionResult):
            return self.content.failures
        else:
            return None

    def _repr_html_(self):
        return self.show()._repr_html_()

    def print_ipython_mathjax(self):
        return self.latex_step_tree()

    def tree(self, derivations=False, recurse=True, style=None):
        return self.build_display_tree(derivations=derivations, recurse=recurse, style=style)

    def show(self,derivations=False, short=True, style=None):
        """Show the step-by-step derivation(s) as a proof tree."""
        if self.content is None:
            return self.build_display_tree(derivations=derivations, style=style)
        elif isinstance(self.content, CompositionResult):
            if short:
                return self.content.show(style=style)
            else:
                return self.content.tree(derivations=derivations, style=style)
        elif len(self.content) == 1:
            return self.content[0].tree(derivations=derivations, style=style)
        else:
            raise NotImplementedError()

    def paths(self,derivations=False, style=None):
        return self.show(derivations=derivations, short=False, style=None)

    def build_display_tree(self, derivations=False, recurse=True, style=None):
        defaultstyle = display.td_proof_style
        style = display.Styled.merge_styles(style, defaultstyle)
        parts = list()
        for i in range(len(self)):
            try:
                part_i = self[i].build_display_tree(recurse=recurse, derivations=derivations, style=style)
            except AttributeError:
                try:
                    part_i = display.RecursiveDerivationLeaf(self[i]._repr_html_(), style=style)
                except AttributeError:
                    part_i = display.RecursiveDerivationLeaf(str(self[i]), style=style)
            parts.append(part_i)
        if self.composed():
            s = self.content.build_summary_for_tree(style=style)
            node = display.RecursiveDerivationLeaf(self.short_str(latex=True, children=False, force_brackets=True), s, style=dict(style, leaf_border="1px"))
        else:
            try:
                node = self.label()._repr_html_()
            except:
                node = str(self.label())
        return display.RecursiveDerivationDisplay(node, explanation=None, parts=parts, style=style)


    def latex_step_tree_r(self, derivations=False):
        if len(self.content) == 1:
            return self.content[0].latex_step_tree_r(derivations=derivations)
        else:
            raise NotImplementedError(repr(self))

    def __mul__(self, other):
        Composable.__mul__(self, other)

    @classmethod
    def from_tree(cls, t, system=None):
        """Factory method to construct a CompositionTree from an nltk.Tree.

        Note that this doesn't convert the whole tree, just the top node."""
        return CompositionTree(t.label(), t, system=system)

    @classmethod
    def tree_factory(cls, composable, system=None):
        """Try to build a CompositionTree from some source.

        Currently, this mainly takes Composables.

        If it receives a string (or a Tree), it will build a (denotation-less) CompositionTree with that string/tree node as the node label.
        If it receives a Composable, it will try to find a way to use that Composable as the denotation, and come up with a node label.
          * The source field will be correctly set in this case.
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
            if isinstance(composable, CompositionTree):
                return composable
            elif isinstance(composable, TreeComposite):
                if composable.source is not None:
                    if isinstance(composable.source, CompositionTree):
                        return composable.source # Composite already derives from some composition tree
                    elif isinstance(composable.source, Tree): # I think this shouldn't happen any more?
                        ct = CompositionTree.from_tree(composable.source, system=system)
                        ct.denotation = [composable,]
                        return ct
                    else:
                        meta.logger.warning("Unknown source '%s' when converting a TreeComposite to a CompositionTree" % repr(composable.source))
                return CompositionTree(composable.name, children=composable.children, denotation=composable, system=system)
            else:
                try:
                    name = composable.composite_name()
                except Exception:
                    name = composable.name # may still fail?
                return CompositionTree(name, children=None, denotation=composable, system=system)
        elif isinstance(composable, Tree):
            return CompositionTree.from_tree(composable, system=system)
        else:
            raise NotImplementedError()


class Composite(SingletonComposable):
    """Abstract class used mainly for single deterministic composition results."""
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
    """A TreeComposite represents a single denotation that results from composition in a tree structure.  It inherits
    from nltk.Tree as well as Composite.

    For multiple denotations or non-determinism, see CompositionTree."""
    def __init__(self, *children, content=None, mode=None, source=None):
        if isinstance(source, Composite) and source.source is not None:
            source = source.source # TODO: recursive?
        if isinstance(content, Composite):
            if mode is None:
                mode = content.mode
            content = content.content
        Composite.__init__(self, children, content, mode=mode, source=source)
        Tree.__init__(self, content, children)
        self.children = self # hack
        self.collapsed_paths = list()
        self.collapsed_count = 1
        for c in children:
            if isinstance(c, TreeComposite):
                self.collapsed_count *= c.collapsed_count
                
    @property
    def p1(self):
        return self[0]

    @property
    def p2(self):
        return self[1]

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
        if self.content is not None and isinstance(self.content, PlaceholderTerm):
            return True
        return False

    def compose_str_latex(self):
        return self.compose_str(latex=True)

    def compose_str(self, latex=False, collapsed=True):
        if isinstance(self.content, Exception):
            if latex:
                try:
                    return self.content.latex_str()
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
                    s += " (%i equivalent paths not shown: %s)" % (len(self.collapsed_paths), cstr)
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

    def derivs_for_tree(self):
        if self.content.derivation is None:
            return None
        l = self.content.derivation.steps_sequence(latex=True, ignore_trivial=True)
        s = "<table>"
        for (step, reason, subexpression) in l:
            s += "<tr><td style=\"padding-right:5px\"> $=$ </td><td style=\"align:left\">%s</td></tr>" % step
        s += "</table>"
        return s

    def derivs_for_tree_rdd(self, content):
        if self.content.derivation is None:
            return None
        l = self.content.derivation.steps_sequence(latex=True, ignore_trivial=True)
        steps = [content,] + [step[0] for step in l]
        return display.RecursiveDerivationLeaf(*steps, style={"leaf_style": "eq"})

    def latex_terminal_tree(self, derivations=False):
        if self.content is None:
            return "<table align=\"center\"><tr><td align=\"center\">%s</td></tr><tr><td align=\"center\"><i>N/A</i></td></tr></table>\n" % (self.short_str_latex())
        else:
            return self.local_latex_tree(derivations=derivations)


    def local_latex_tree(self, mode=True, derivations=False):
        if derivations and self.content.derivation is not None:
            content_str = self.derivs_for_tree() #self.content.derivation.latex_steps_str()
        else:
            if self.placeholder():
                content_str = ensuremath(self.content.latex_str())
            else:
                content_str = ensuremath(" = " + self.content.latex_str())
        if self.placeholder():
            s = "<table style=\"margin-top:10px\"><tr><td style=\"vertical-align:bottom\" align=\"center\">%s</td>" % (content_str)
        else:
            s = "<table style=\"margin-top:10px\"><tr><td style=\"vertical-align:bottom\" align=\"center\">%s</td></tr><tr><td style=\"vertical-align:bottom\" align=\"center\">%s</td>" % (self.short_str_latex(), content_str)
        s += "</tr></table>\n"
        return s

    def latex_step_tree_r(self, derivations=False):
        child_cells = []
        for i in range(len(self)):
            if not isinstance(self[i], Composable):
                continue # TODO: revisit.  Right now allowing Trees here should work, but instead produces odd visual problems.
            if isinstance(self[i], str):
                str_i = self[i]
            else:
                str_i = self[i].latex_step_tree_r(derivations=derivations)
            child_cells.append("<td style=\"vertical-align:bottom\">%s</td>" % str_i)
        if len(child_cells) == 0:
            return self.latex_terminal_tree(derivations=derivations)
        s = "<table><tr><td style=\"vertical-align:bottom;padding:0px 10px\" align=\"center\">" 
        s += "<table><tr>"
        s+= "<td style=\"vertical-align:bottom;padding-bottom:5px\">&nbsp;&nbsp;&nbsp;$\circ$&nbsp;&nbsp;&nbsp;</td>".join(child_cells)
        s += "</tr></table></td>"
        if self.mode is None:
            s += "</tr>"
        else:
            s += "<td style=\"vertical-align:bottom;padding-bottom:5px;padding-left:10px\"><b>[%s]</b></td></tr>" % self.mode.name
        s += "<tr style=\"border-top: 1px solid #848482\"><td align=\"center\">%s</td><td></td></tr></table>\n" % self.local_latex_tree(derivations=derivations)
        return s

    def build_display_tree(self, derivations=False, recurse=True, style=None):
        defaultstyle = display.td_box_style
        style = display.Styled.merge_styles(style, defaultstyle)
        parts = list()
        for i in range(len(self)):
            if not isinstance(self[i], Composable):
                continue
            if isinstance(self[i], str):
                part_i = display.RecursiveDerivationDisplay(self[i], style=style)
            else:
                part_i = self[i].build_display_tree(derivations=derivations, recurse=recurse, style=style)
            parts.append(part_i)
        if self.content:
            content_str = utils.ensuremath(self.content.latex_str())
        else:
            content_str = "N/A"
        if self.placeholder():
            node_content = display.RecursiveDerivationLeaf(content_str, style=style)
            expl = None
        else:
            if self.mode:
                if isinstance(self.mode, str):
                    expl = self.mode
                else:
                    expl = self.mode.name
                collapsed = self.collapsed_compose_str()
                if len(collapsed) > 0:
                    expl += "<span style=\"font-size:x-small\"> (or: " + self.collapsed_compose_str() + ")</span>"
            else:
                expl = None
            # TODO revisit and generalize this (maybe override Item in a better way?)
            if expl and len(parts) == 0:
                # no subparts but there is an explanation.  This is the case of a leaf node derived from a tree.
                # show the short str in the slot for a part
                parts.append(display.RecursiveDerivationLeaf(self.short_str_latex(), style=style))
                if derivations and self.content.derivation is not None:
                    node_content = self.derivs_for_tree_rdd(None)
                else:
                    node_content = display.RecursiveDerivationLeaf(content_str, style=style)
            else:
                if derivations and self.content.derivation is not None:
                    node_content = self.derivs_for_tree_rdd(self.short_str_latex()) #self.content.derivation.latex_steps_str()
                else:
                    node_content = display.RecursiveDerivationLeaf(self.short_str_latex(), content_str, style=style)
        return display.RecursiveDerivationDisplay(node_content, explanation=expl, parts=parts, style=style)

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
                return self.source

    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as possible."""
        self.content = self.content.reduce_all().simplify_all()
        return self

    def _repr_latex_(self):
        # since this inherits from Tree, need to ensure that we don't inherit a monkey-patched _repr_latex_ from there.
        return self.latex_str()

    def _repr_html_(self):
        return self.latex_str()

class BinaryComposite(TreeComposite):
    def __init__(self, p1, p2, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, p2, content=content, mode=mode, source=source)

class UnaryComposite(TreeComposite):
    def __init__(self, p1, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, content=content, mode=mode, source=source)

class CompositionResult(Composable):
    """Container class for a stage of a composition.  Can represent multiple composition paths, and tracks
    failures."""
    def __init__(self, items, results, failures, source=None):
        """Construct a CompositionResult given the output of the things that can happen while doing composition.

        `items`: a list of Composables that were the input to the CompositionStep.  These might themselves be CompositionResults.
        `results`: a list of results from composition.
        `failures`: a list of failed composition paths, usually in the form of information-rich TypeMismatch objects.
        `source`: some representation of a natural language structure that led to this composition step.

        """
        self.items = items
        self.failures = failures
        self.source = source
        self.result_hash = dict()
        self.results = list()
        for r in results:
            self.add_result(r)

    def __repr__(self):
        return "CompositionResult(results=%s, failures=%s)" % (repr(self.results), repr(self.failures))
        if len(self.results) == 0:
            return repr(self.failures)
        else:
            return repr(self.result_items())

    def __str__(self):
        s = str()
        if (len(self.results) == 0):
            s += "Composition failed.  Attempts:\n"
            s += self.failures_str()
        else:
            for composite in self.results:
                s += "    " + composite.compose_str()
        return s

    def show(self, recurse=True, style=None, failures=False):
        s = str()
        if (len(self.results) == 0):
            if self.source is None:
                s += "Composition failed.  Attempts:<br />\n"
            else:
                s += "Composition of %s failed.  Attempts:<br />\n" % self.source.short_str(latex=True)
            s += self.failures_str_latex()
        else:
            if (len(self.results) == 1):
                s += "1 composition path.  Result:"
            else:
                s += "%i composition paths. Results:" % len(self.results)
            n = 0
            for composite in self.results:
                #TODO: newlines in mathjax??
                num = composite.collapsed_count
                if num == 1:
                    s += "\n<br />" + latex_indent() + "[%i]: " % n + composite.latex_str()
                else:
                    s += "\n<br />" + latex_indent() + "[%i]: %s &nbsp;&nbsp;<span style=\"font-size:small\">(%i equivalent paths lead here)</span>" % (n, composite.latex_str(), num)
                n += 1
            if failures:
                s += "\n<br /><br />" + "Composition attempts that failed:<br />\n" + self.failures_str_latex()
        return MiniLatex(s)

    def build_summary_for_tree(self, style=None):
        defaultstyle = display.td_box_style
        style = display.Styled.merge_styles(style, defaultstyle)
        if len(self.results) == 0:
            return display.RecursiveDerivationLeaf("Composition failure", style=dict(style, leaf_style="alert"))
        elif len(self.results) == 1:
            return display.RecursiveDerivationLeaf(self.results[0].latex_str(), style=dict(style, leaf_align="center"))
        else:
            n = 0
            parts = list()
            for composite in self.results:
                parts.append("<span style=\"color:blue\">[path %i]</span>: &nbsp;" % n + composite.latex_str())
                n += 1
            return display.RecursiveDerivationLeaf(*parts, style=style)

    def failures_str_latex(self):
        return self.failures_str(latex=True)

    def failures_str(self, latex=False):
        s = str()
        for f in self.failures:
            if isinstance(f, CompositionResult):
                s += "Inheriting composition failure.  "
                if latex:
                    s += f.latex_str()
                else:
                    s += str(f)
            elif isinstance(f, Composite):
                if latex:
                    s += latex_indent() + f.content.latex_str() + "<br />\n"
                else:
                    s += "    " + str(f.content) + "\n"
            else:
                raise NotImplementedError()
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
            s += "No successful paths -- tracing failures...<br />\n" + self.failures_trace_latex()
            return s
        elif len(self.results) == 1:
            s += "1 path:<br />\n"
        else:
            s += "%i paths:<br />\n" % len(self.results)
        for r in self.results:
            spcount = r.collapsed_count #len(r.collapsed_paths)
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
                            spstr = " (%i equivalent sub-paths not shown)" % (spcount - 1)
                    else:
                        spstr = ""
                    s += "<b>Path %i%s:</b><br />\n" % (i, spstr)
                for step in steps:
                    if step is path:
                        s += latex_indent() + ("Step %i: " % step_i) + step.compose_str(latex=True, collapsed=(not subpaths)) + "<br />\n"
                    else:
                        s += latex_indent() + ("Step %i: " % step_i) + step.compose_str(latex=True) + "<br />\n"
                    step_i += 1
                sub_i += 1
            i += 1
        return meta.MiniLatex(s)

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
            # this will return a MiniLatex-packaged string.
            rst = r.tree(derivations=derivations, recurse=recurse, style=style)
            s += rst._repr_html_() + "<br /><br />"
            i += 1
        return MiniLatex(s)

    def build_display_trees(self, recurse=True, derivations=False, style=None):
        defaultstyle = display.td_box_style
        style = display.Styled.merge_styles(style, defaultstyle)

        if len(self.results) == 0:
            return display.RecursiveDerivationLeaf("No succesful composition paths.", style=style)
        else:
            rows = list()
            if len(self.results) == 1:
                rows.append("1 composition path:")
            else:
                rows.append("%i composition paths:\n" % len(self.results))
            i = 0
            for r in self.results:
                if len(self.results) > 1:
                    rows.append("Path [%i]:\n" % i)
                rst = r.build_display_tree(derivations=derivations, recurse=recurse, style=style)
                rows.append(rst)
                rows.append("<br />")
                i += 1
            return display.RecursiveDerivationLeaf(*rows, style=dict(style, leaf_align="left"))



    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as possible."""

        # this is a bit complicated because reducing in place may change the hash of any results. (not to mention collapse results)
        # it's generally better to just enable reduction in the composition system.
        rcopy = list(self.results)
        dirty = False
        for r in rcopy:
            old_c = r.content
            new_c = r.content.reduce_all().simplify_all()
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

    def __getitem__(self, i):
        return self.results[i]

    def add_result(self, r):
        if r.content in self.result_hash:
            self.result_hash[r.content].extend_collapsed_paths(r)
        else:
            self.result_hash[r.content] = r
            self.results.append(r)

    def extend(self, other):
        """Extend this with another CompositionResult."""
        if not isinstance(other, CompositionResult):
            raise ValueError
        for r in other.results:
            self.add_result(r)
        self.failures.extend(other.failures)

    def prune(self, i, reason=None):
        """Remmove result `i` with some specified `reason`.

        Will move the derivation into the `failures` list."""
        result = self.results[i]
        del self.result_hash[result.content]
        del self.results[i]
        self.failures.append(result)
        #TODO: do something with reason

class CRFilter(object):
    """A filter on CompositionResults that enforces some specified meta-language criteria."""
    def __init__(self, name, filter_fun):
        """Construct a filter on CompositionResults.

        `name`: the name of the filter.
        `filter_fun`: a function that implements the filter on a single TypedExpr.

        The simplest case would be e.g. to check that a derivation has a specific type."""
        self.filter_fun = filter_fun
        self.name = name

    def __call__(self, cresult):
        i = 0
        while i < len(cresult.content):
            passes = self.filter_fun(cresult.content[i].content)
            if passes:
                i += 1
            else:
                cresult.prune(i, reason=self.name)
        return cresult

class Item(TreeComposite):
    """This class represents a lexical item.  It is implemented as a TreeComposite without a daughter."""
    def __init__(self, nl_name, content, index=None, mode=None):
        """Construct an Item.

        `nl_name`: the natural language name of the Item.
        `content`: a TypedExpr content for the item.
        `index`: the index, if any.  (For traces, etc)
        `mode`: passed to superclass (not currently used).
        """
        TreeComposite.__init__(self, content=content, mode=mode)
        #self.content = TypedExpr.ensure_typed_expr(content)
        self.__node_name__ = nl_name
        if index is None:
            self.index = None
        else:
            if index > 0:
                self.index = index
            else:
                self.index = 0

    @property
    def constant(self):
        return not self.placeholder()

    def copy(self):
        return Item(self.name, self.content.copy(), self.index)

    def reduce_all(self):
        """Replace contents with versions that have been reduced as much as possible."""
        self.content = self.content.reduce_all().simplify_all()
        return self

    def reduce(self):
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
            a2 = assignment.copy()
            a2["index"] = index
            return self.content.under_assignment(assignment)

    def latex_step_tree_r(self, derivations=False):
        if self.content is None:
            return "<table align=\"center\"><tr><td align=\"center\">%s</td></tr><tr><td align=\"center\"><i>N/A</i></td></tr></table>\n" % (self.short_str_latex())
        else:
            return "<table align=\"center\"><tr><td align=\"center\">%s</td></tr><tr><td align=\"center\">%s</td></tr></table>\n" % (self.short_str_latex(), ensuremath(self.content.latex_str()))

    def build_display_tree(self, derivations=False, recurse=None, style=None):
        defaultstyle = display.td_box_style
        style = display.Styled.merge_styles(style, defaultstyle)
        if not self.content:
            return display.RecursiveDerivationLeaf(self.short_str_latex(), "N/A", style=style)
        else:
            return super().build_display_tree(derivations=derivations, recurse=recurse, style=style)

class CompositionOp(object):
    """A unary composition operation."""
    def __init__(self, name, operation, desc=None, latex_desc=None, composite_name=None, allow_none=False, reduce=False, system=None):
        """Build a composition operation given some function.  See also `unary_factory`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take one Composables and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from the operands.
        `allow_none`: can the argument to `operation` have content None?
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be set/changed automatically if this operation is added to a system.)
        """
        self.operation = operation
        self.__name__ = name
        self.allow_none = allow_none
        if composite_name is not None:
            self.composite_name = composite_name
        if system is not None:
            self.system = system
        self.reduce = reduce # shadows builtin
        self.desc = desc
        self.latex_desc = latex_desc

    def _repr_html_(self):
        if self.latex_desc is None:
            return "%s <i>%s</i>, built on python function '%s.%s'" % (self.description(), self.name, self.operation.__module__, self.operation.__name__)
        else:
            return "%s <i>%s</i>, built on combinator '%s'" % (self.description(), self.name, self.latex_desc)

    def __repr__(self):
        if self.desc is None:
            return "%s %s, built on python function '%s.%s'" % (self.description(), self.name, self.operation.__module__, self.operation.__name__)
        else:
            return "%s %s, built on combinator '%s'" % (self.description(), self.name, self.desc)

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
    def __init__(self, name, operation, commutative=False, desc=None, latex_desc=None,  composite_name=None, allow_none=False, reduce=False, system=None):
        """Build a composition operation given some function.  See also `binary_factory` and `binary_factory_curried`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take two Composables and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from the operands.
        `allow_none`: can either of the arguments to `operation` have content None?  (See e.g. the PA rule.)
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be set/changed automatically if this operation is added to a system.)
        """
        super().__init__(name, operation, desc=desc, latex_desc=latex_desc, composite_name=composite_name, allow_none=allow_none, reduce=reduce, system=system)
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
            raise TypeMismatch(i1, i2, self.name)
        result = self.operation(i1, i2, assignment=assignment)
        result.mode = self
        if self.reduce:
            result = result.reduce_all()
        return result

    def description(self):
        return "Binary composition rule"

class UnaryCompositionOp(CompositionOp):
    """A unary composition operation."""
    def __init__(self, name, operation, typeshift=False, desc=None, latex_desc=None, composite_name=None, allow_none=False, reduce=False, system=None):
        """Build a composition operation given some function.  See also `unary_factory`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take one Composables and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from the operands.
        `allow_none`: can the argument to `operation` have content None?
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be set/changed automatically if this operation is added to a system.)
        """
        super().__init__(name, operation, desc=desc, latex_desc=latex_desc, composite_name=composite_name, allow_none=allow_none, reduce=reduce, system=system)
        self.typeshift = typeshift

    @property
    def arity(self):
        return 1

    def composite_name(self, i1):
        return "[%s]" % (i1.name)

    def __call__(self, i1, assignment=None):
        # handle None here, rather than in all individual functions.
        if (not self.allow_none) and (i1.content is None):
            raise TypeMismatch(i1, None, self.name)
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

class CombinatorCompositionOp(CompositionOp):
    def __init__(self, name, combinator, arity=1, typeshift=False, commutative=False, desc=None, latex_desc=None,  composite_name=None, allow_none=False, reduce=False, system=None):
        """Build a composition operation given some function.  See also `binary_factory` and `binary_factory_curried`.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take two Composables and an optional assignment.
        `commutative`: should the operation be tried in both orders?
        `composite_name`: an optional function to determine the node name from the operands.
        `allow_none`: can either of the arguments to `operation` have content None?  (See e.g. the PA rule.)
        `reduce`:  should `reduce_all` be called on the result?
        `system`: the composition system that this is part of.  (Will be set/changed automatically if this operation is added to a system.)
        """
        self.combinator = combinator
        self._arity = arity
        if arity == 1:
            fun = self.unary_call
        elif arity == 2:
            fun = self.binary_call
        else:
            raise NotImplementedError
        super().__init__(name, fun, desc=desc, latex_desc=latex_desc, composite_name=composite_name, allow_none=allow_none, reduce=reduce, system=system)
        self.commutative = commutative
        self.typeshift = typeshift

    @property
    def arity(self):
        return self._arity

    def unary_call(self, i1, assignment=None):
        result = self.combinator(arg.content.under_assignment(assignment))
        return UnaryComposite(arg, result)

    def op_fun(arg1, arg2, assignment=None):
        result = self.combinator(arg1.content.under_assignment(assignment))(arg2.content.under_assignment(assignment))
        return BinaryComposite(arg1, arg2, result)


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
    def __init__(self, name, operation, preconditions=None, commutative=False, allow_none=False, reduce=True, system=None):
        """Build a composition operation on trees given some function.

        `name`: the name of the operation, e.g. "FA".
        `operation`: a function implementing the operation.  Must take a tree structure and an optional assignment.
        `preconditions`: a function that checks some preconditions on a tree structure, returning a binary.  Defaults to checking binarity.
        `commutative`: should the operation be tried in both orders?  NOTE: currently not used.
        `allow_none`: can some node have content None?
        `system`: the composition system that this is part of.  (Will be set/changed automatically if this operation is added to a system.)
        """
        self.operation = operation
        self.__name__ = name
        self.commutative = commutative
        self.allow_none = allow_none
        if preconditions is None:
            self.preconditions = tree_binary
        else:
            self.preconditions = preconditions
        self.system = system # adding the rule to a system will set this, no need to pre-check
        self.reduce = reduce
        self.typeshift = False
        self.latex_desc = None
        self.desc = None

    @property
    def name(self):
        return self.__name__

    @property
    def arity(self):
        return 1

    def description(self):
        return "Tree composition rule"

    def composite_name(self, t):
        return t.label()

    def __str__(self):
        return "Tree composition op '%s'" % self.name

    def _repr_html_(self):
        if self.latex_desc is None:
            return "%s <i>%s</i>, built on python function '%s.%s'" % (self.description(), self.name, self.operation.__module__, self.operation.__name__)
        else:
            return "%s <i>%s</i>, built on combinator '%s'" % (self.description(), self.name, self.latex_desc)

    def __repr__(self):
        if self.desc is None:
            return "%s %s, built on python function '%s.%s'" % (self.description(), self.name, self.operation.__module__, self.operation.__name__)
        else:
            return "%s %s, built on combinator '%s'" % (self.description(), self.name, self.desc)


    # this could be a classmethod, as it doesn't reference anything on an instance.  Old version
    # did reference the composition system, however, and this may need to be revisited.  (See CompositionTree.build_local_tree)
    def build_local(self, tree):
        """Convert an arbitrary Tree into a local tree where all children are Composables.

        Uses PlaceholderTerm for subtrees which are not yet composed.

        This function is idempotent."""
        if not isinstance(tree, CompositionTree):
            tree = CompositionTree.tree_factory(tree)
        tree.build_local_tree(override=False)
        return tree

    def __call__(self, tree, assignment=None):
        test = self.preconditions(tree)
        if not test:
            #return None
            raise TypeMismatch(tree, None, mode="Failed preconditions for %s" % self.name)
        if (not self.allow_none):
            for d in tree:
                if d.content is None:
                    raise TypeMismatch(tree, None, mode="None not allowed for %s" % self.name) 
        result = self.operation(tree, assignment=assignment)
        if self.reduce:
            result = result.reduce_all()
        result.mode = self
        return result


class LexiconOp(TreeCompositionOp):
    """A composition operation that looks up a lexical entry in the composition system's lexicon."""
    def __init__(self, system=None):
        TreeCompositionOp.__init__(self, "Lexicon", self.lookup, preconditions=tree_leaf, system=system)

    def lookup(self, t, assignment=None):
        # TODO: revisit
        if isinstance(t, TreeComposite) and t.label() is None and t.source is not None:
            name = t.source.label()
        elif t.label() and isinstance(t.label(), PlaceholderTerm) and t.source is not None:
            name = t.source.label()
        else:
            assert(isinstance(t.label(), str))
            name = t.label()
        den = self.system.lookup_item(name)
        if den is None:
            raise TypeMismatch(t, None, mode="No lexical entry for '%s' found." % name)
        return den

def unary_factory(meta_fun, name, typeshift=False, reduce=True):
    """Factory function to construct a unary composition operation given some function.

    This is extremely useful for building unary operations and type-shifts from meta-language combinators.
    """
    def op_fun(arg, assignment=None):
        result = meta_fun(arg.content.under_assignment(assignment))
        return UnaryComposite(arg, result)
    desc = None
    latex_desc = None
    if isinstance(meta_fun, meta.TypedExpr):
        desc = repr(meta_fun)
        latex_desc = meta_fun._repr_latex_()
    return UnaryCompositionOp(name, op_fun, typeshift=typeshift, reduce=reduce, desc=desc, latex_desc=latex_desc)

def binary_factory(meta_fun, name, reduce=True, combinator_source=None):
    """Factory function to construct a binary composition operation given some function."""
    def op_fun(arg1, arg2, assignment=None):
        result = meta_fun(arg1.content.under_assignment(assignment), arg2.content.under_assignment(assignment))
        return BinaryComposite(arg1, arg2, result)
    desc = None
    latex_desc = None
    if combinator_source is not None:
        desc = repr(combinator_source)
        latex_desc = combinator_source._repr_latex_()
    return BinaryCompositionOp(name, op_fun, reduce=reduce, desc=desc, latex_desc=latex_desc)

def binary_factory_curried(meta_fun, name, reduce=True, commutative=False):
    """Factory function to construct a binary composition operation given some (curried) function.

    This is extremely useful for building operations from meta-language combinators.  For example, PM can be implemented using just:
    >lang.binary_factory_curried(lang.pm_op, "PM")
    """
    def op_fun(arg1, arg2, assignment=None):
        result = meta_fun(arg1.content.under_assignment(assignment))(arg2.content.under_assignment(assignment))
        return BinaryComposite(arg1, arg2, result)
    desc = None
    latex_desc = None
    if isinstance(meta_fun, meta.TypedExpr):
        desc = repr(meta_fun)
        latex_desc = meta_fun._repr_latex_()
    return BinaryCompositionOp(name, op_fun, commutative=commutative, reduce=reduce, desc=desc, latex_desc=latex_desc)




class PlaceholderTerm(meta.TypedTerm):
    """This class represents a placeholder for some denotation  that is unknown or not yet composed.  The primary use
    is in incrementally doing top-down composition."""
    def __init__(self, varname, placeholder_for, system=None, assignment=None, type_check=True):
        meta.TypedTerm.__init__(self, varname, types.UnknownType(), assignment=assignment, type_check=type_check)
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
        """the content of the placeholder is either a string, or a nltk Tree, in which case the name is taken from its 'node' field.
        """
        if isinstance(self.placeholder_for, str):
            return self.placeholder_for
        else:
            return self.placeholder_for.label()


    def latex_str(self):
        return ensuremath(inbrs(self.placeholder_name(), self.assign_controller.render(latex=True)) + "_{" + self.type.latex_str() + "}")

    def __repr__(self):
        # TODO: make this parse?
        return text_inbr(self.placeholder_name()) + self.assign_controller.render(latex=False)

    def expand(self):
        """Attempt to expand the node by composing whatever `self` is a placeholder for.

        If this composition is already done, just return the result.  (E.g. this is memoized.)"""
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
        return self.local_copy(self.op)

    def local_copy(self, op, type_check=True):
        result = PlaceholderTerm(op, self.placeholder_for, system=self.system, type_check=type_check)
        result.let = self.let
        result.type = self.type # type may have changed, e.g. via alphabetic conversion to a fresh type
        return result





class CompositionSystem(object):
    """A CompositionSystem describes an overarching way of dealing with semantic composition, made up of composition
    rules/operations, types, and a lexicon."""
    def __init__(self, rules=None, basictypes = None, name=None, a_controller=None):
        self.rules = list()
        self.ruledict = dict()
        for r in rules:
            self.add_rule(r)

        if basictypes is None:
            self.basictypes = set()
        else:
            self.basictypes = basictypes
        self.name = name

        if a_controller is None:
            self.assign_controller = VacuousAssignmentController()
        else:
            self.assign_controller = a_controller
        self.typecache = set()
        self.lexicon = dict()
        self.update_typeshifts()
        self.typeshift_depth = 3
        self.typeshift = False

    def copy(self):
        """Make a copy of the composition system."""
        new_sys = CompositionSystem(rules=self.rules, basictypes=self.basictypes, name=(self.name + " (copy)"), a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon
        return new_sys

    def add_rule(self, r):
        """Add a composition rule.  `r` should be a CompositionOp of some kind."""
        r.system = self
        if r.name is not None:
            if r.name in self.ruledict.keys():
                meta.logger.warning("Composition rule named '%s' already present in system" % r.name)
            self.ruledict[r.name] = r
        self.rules.append(r)
        self.update_typeshifts()

    def add_unary_rule(self, combinator, name, reduce=True):
        rule = unary_factory(combinator, name, reduce=reduce)
        self.add_rule(rule)
        return rule

    def add_binary_rule(self, combinator, name, reduce=True, commutative=False):
        rule = binary_factory_curried(combinator, name, reduce=reduce, commutative=commutative)
        self.add_rule(rule)
        return rule

    def add_binary_rule_uncurried(self, fun, name, reduce=True, combinator_source=None):
        rule = binary_factory(fun, name, reduce=reduce, combinator_source=combinator_source)
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
            meta.logger.warning("Composition rule '%s' not found in system" % name)
            return
        del self.ruledict[name]
        self.rules = [r for r in self.rules if r.name != name]
        self.update_typeshifts()

    def get_rule(self, r):
        """return a composition rule by name.  Note that some properties are cached, in particular typeshifting.

        In general it may be safest to re-add a rule after modifying it."""
        if isinstance(r, str):
            name = r
        else:
            name = r.name
        return self.ruledict[name]

    # TODO: function for checking if system supports an arbitrary type

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
        return self.description(latex=True)

    def lookup(self, *items):
        """Look up a sequence of potential lexical items, replacing any that have one with their lexical entry."""
        r = list()
        for i in items:
            try: # this is to catch the case where i is unhashable...couldn't find a better way of doing it.  Comes up because of Tree.
                if i in self.lexicon:
                    r.append(self.lexicon[i])
                else:
                    r.append(i)
            except TypeError:
                r.append(i)
        return r

    def lookup_item(self, i):
        """Look up a single lexical item `i`.  Currently, `i` should be a string."""
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
        """Compose the items according to the system.  Each item may be a container object."""
        return self.compose_iterables(*items, assignment=assignment, block_typeshift=block_typeshift)

    def do_typeshifts(self, item, depth=1, include_base=True, assignment=None):
        """Given some Composable `item`, try type-shifting it.

        `item`: a Composable to manipulate.
        `depth`: a max depth to search.  (Defaults to 1.  Loops are possible.)
        `include_base`: should the resulting list include the starting `item`?
        `assignment`: an optional assignment to pass to composition operations.

        Returns a composition result containing any type-shifted denotations, plus the base `item` depending on `include_base`.
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
            l = new_l
        l = new_l
        if include_base:
            l.append(item)
        return CompositionResult([item], l, list())


    def compose_raw(self, *items, assignment=None, block_typeshift=False):
        """Attempts to compose the provided items.  This is the 'raw' version not intended to be called directly, and 
        assumes that non-determinism is already taken care of.

        Brute force tries every composition rule and order of items.  Note that currently this not handle arities > 2.
        """
        from lamb import parsing
        results = list()
        failures = list()
        items = self.lookup(*items)
        arity = len(items)
        for mode in self.rules:
            if arity != mode.arity:
                #TODO: put something in failure list?
                continue
            if arity == 1:
                if mode.typeshift:
                    continue
                orders = ((items[0],),)
            elif arity == 2:
                if mode.commutative:
                    orders = ((items[0], items[1]),)
                else:
                    orders = ((items[0], items[1]), (items[1], items[0]))
            else:
                raise NotImplementedError
            for order in orders:
                try:
                    #print(order)
                    result = mode(*order, assignment=assignment)
                    if arity == 1:
                        if isinstance(order[0], Tree):
                            result.c_name = order[0].label()
                        else:
                            result.c_name = order[0].name
                    else:
                        result.c_name = mode.composite_name(items[0], items[1])
                    results.append(result)
                except (TypeMismatch, parsing.ParseError) as e:
                    if isinstance(e, parsing.ParseError):
                        if e.e and isinstance(e.e, TypeMismatch):
                            # extract TypeMismatches that lead to ParseErrors somewhere in the composition operation.
                            # this is coming up when building combinators using te
                            e = e.e
                        else:
                            print("test ", e.e, ", ", isinstance(e.e, TypeMismatch), ", ", e)
                            raise e
                    #print(e)
                    if arity == 1:
                        failures.append(Composite(order[0], e, mode=mode))
                    else:
                        failures.append(BinaryComposite(order[0], order[1], e, mode=mode))
                    continue
        # typeshift as a last resort
        if len(results) == 0 and self.typeshift and not block_typeshift:
            shift_result = self.last_resort_shift(*items, assignment=assignment)
            if shift_result is not None and len(shift_result.results) > 0:
                return shift_result
        ret = CompositionResult(items, results, failures)
        return ret


    def last_resort_shift(self, *items, assignment=None):
        """Do last-resort style typeshifting (up to a constant depth).  That is, while (non-type-shifting) composition fails, try typeshifting
        deeper and deeper until finding some things that compose succesfully.

        The depth is determined by `self.typeshift_depth`.  Depending on the shifts, setting this high may result in exponential blowup.

        `items`: the Composable(s) that would be passed to a CompositionOp.
        `assignment`: an optional assignment to pass to composition operations.

        Returns a composition result or None."""
        for i in range(1, self.typeshift_depth):
            new_items = list(items)
            typeshifts_changed = False
            for n in range(len(new_items)):
                new_i_n = self.do_typeshifts(new_items[n], depth=i, assignment=assignment)
                new_items[n] = new_i_n
                if len(new_i_n.results) > 1:
                    typeshifts_changed = True
            if typeshifts_changed:
                result = self.compose(*new_items, assignment=assignment, block_typeshift=True)
                if len(result.results) > 0:
                    return result
        return None


    #def compose(self, i1, i2):
    #    return self.compose_long(i1, i2).result_items()

    def compose_iterables(self, t1, t2=None, assignment=None, block_typeshift=False):
        """Compose one or two iterables `t1` and `t2` (optional).  Don't call directly."""
        iter1 = t1.content_iter()
        if t2 is None:
            iter2 = None
        else:
            iter2 = t2.content_iter()
        r = self.compose_iterators(iter1, iter2, assignment=assignment, block_typeshift=block_typeshift)
        return r

    def compose_iterators(self, iter1, iter2=None, assignment=None, block_typeshift=False):
        """Compose one or two iterators.  Do not call directly."""
        r = CompositionResult(None, [],[])
        if iter2 is None:
            for i1 in iter1:
                r.extend(self.compose_raw(i1, assignment=assignment, block_typeshift=block_typeshift))
        else:
            # this seems like not the best way to do this...but can't use iter2 directly because there's no
            # way to reset it.  I considered itertools.tee, but the docs suggested that lists are more efficient
            # for this case.
            list_i2 = list(iter2)
            for i1 in iter1:
                for i2 in list_i2:
                    r.extend(self.compose_raw(i1, i2, assignment=assignment, block_typeshift=block_typeshift))
        return r

    def compose_container(self, c, assignment=None, block_typeshift=False):
        """Compose a container `c`.  Intended for use with a CompositionTree."""
        r = self.compose_iterators(c.flatten_iter(), assignment=assignment, block_typeshift=block_typeshift)
        if r.empty() and len(r.failures) == 0:
            r.failures.extend(c.find_empty_results()) # find any errors inherited from subtrees.
        r.source = c
        return r

class TreeCompositionSystem(CompositionSystem):
    """A composition system for doing composition in tree structures."""
    def __init__(self, rules=None, basictypes = None, name=None, a_controller=None):
        CompositionSystem.__init__(self, rules, basictypes, name, a_controller)
        self.add_rule(LexiconOp(system=self))

    def copy(self):
        new_sys = TreeCompositionSystem(rules=self.rules, basictypes=self.basictypes, name=self.name, a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon
        return new_sys

    # Notes on how composition expansion should work in tree structures
    #
    # expansion use cases:
    # 1. fully automated.
    #    When handed a tree, produce a complete-as-possible CompositionResult for the whole tree.
    #
    # 2. programmatic stepwise expansion.
    #    For interaction at CLI or ipython notebook.  Given a tree that is partly or not at all composed, 
    #    expand the tree one node at a time.
    #     * Support any order of nodes.
    #     * Provide default orders, so that an "expand_next" function is feasible.  Need: top down bf / df, bottom up.
    #
    # 3. point and click.
    #    long term goal: javascript interface for clicking on a node in a tree and expanding in place.  (what to do about ambiguities?)
    #
    # Crucial issue for 2,3: relationship of source tree with CompositionResult.

    def td_df_lr_gen(self, tree, parent, path_from_par, len_fun, full_path=None):
        """A generator function that expands a tree in depth-first left-to-right order.  See `search_for_unexpanded` for a use-case.

        Not really intended to be called directly.

        `tree`: the tree to expand.
        `parent`: the immediate parent of the tree, if any.
        `path_from_par`: the index of this node relative to the parent, if any.
        `len_fun`: a function that provides a length operation on a tree node.
        `full_path`: the path from the starting point in the tree, if any.  Call with `None` initially (used in recursion).

        yields a 4-tuple, consisting of a tree node, the parent (if any), the immediate path from the parent, if any, and the full path from the top of the tree.
        """
        # TODO: rethink this
        if full_path is None:
            full_path = tuple()
        yield (tree, parent, path_from_par, full_path)
        if len_fun(tree) == 0:
            raise StopIteration()
        elif len_fun(tree) >= 1:
            for i in range(len_fun(tree)):
                yield from self.td_df_lr_gen(tree[i], tree, i, len_fun, full_path=full_path + (i,))

    def bu_df_lr_gen(self, tree, parent, path_from_par, len_fun, full_path=None):
        if full_path is None:
            full_path = tuple()
        if len_fun(tree) == 0:
            yield (tree, parent, path_from_par, full_path)
        elif len_fun(tree) >= 1:
            for i in range(len_fun(tree)):
                yield from self.bu_df_lr_gen(tree[i], tree, i, len_fun, full_path=full_path + (i,))
            yield (tree, parent, path_from_par, full_path)


    def tree_factory(self, composable):
        return CompositionTree.tree_factory(composable, system=self)

    def simple_composite_name(self, n1, n2):
        return "[%s %s]" % (n1, n2)

    def binary_tree_factory(self, c1, c2):
        t1 = self.tree_factory(c1)
        t2 = self.tree_factory(c2)
        return CompositionTree(self.simple_composite_name(t1.label(), t2.label()), children=[t1, t2], system=self)

    def compose(self, c1, c2=None, override=False, assignment=None):
        if c2 is None:
            tree = self.tree_factory(c1)
        else:
            tree = self.binary_tree_factory(c1, c2)
        return tree.compose(assignment=assignment)

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
        """Convenience wrapper around expansion functions.  Uses top-down left-to-right expansion order to find a node that has not been expanded.
        (stands for 'quick search for unexpanded')"""
        if order is None:
            order = self.bu_df_lr_gen
        return self.search_for_unexpanded(tree, order, self.is_expanded, self.len_fun)

    def compose_path(self, root, path, assignment=None):
        return root.compose_path(path, assignment=assignment)

    def expand_next(self, tree):
        """Convenience wrapper around expansion functions.  Expands whatever `qsfu` finds in tree."""
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




def te(s, assignment=None):
    """Convenience wrapper around the meta-language parser."""
    return meta.TypedExpr.factory(s, assignment=assignment)

def tp(s):
    """Convenience wrapper around the type parser."""
    ts = meta.get_type_system()
    result = ts.type_parser(s)
    return result


def tree_fa_fun_abstract(f, a, assignment=None):
    """Do function application in a fixed function, argument order."""
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(f, a):
        return None
    result = (f.content.under_assignment(assignment))(a.content.under_assignment(assignment))
    return result

def tree_left_fa_fun(t, assignment=None):
    """Given some tree node `t`, do FA assuming the left branch is the function."""
    result = tree_fa_fun_abstract(t[0], t[1], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/left")
    return BinaryComposite(t[0], t[1], result, source=t)

def tree_right_fa_fun(t, assignment=None):
    """Given some tree node `t`, do FA assuming the right branch is the function."""
    result = tree_fa_fun_abstract(t[1], t[0], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/right")
    return BinaryComposite(t[0], t[1], result, source=t)

def tree_nn_fun(t, assignment=None):
    return UnaryComposite(t[0], content=t[0].content.under_assignment(assignment), source=t)


# combinator for predicate modification
pm_op = te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")

def tree_pm_fun(t, assignment=None):
    """H&K predicate modification -- restricted to type <et>.

    This implementation uses the combinator `pm_op` to perform PM via function application.
    """
    ts = meta.get_type_system()
    if not (ts.eq_check(t[0].type, type_property) and 
            ts.eq_check(t[1].type, type_property)):
        raise TypeMismatch(t[0], t[1], "Predicate Modification")
    try:
        varname = t[0].content.varname
    except AttributeError:
        varname = "x"
    c1 = t[0].content.under_assignment(assignment)
    c2 = t[1].content.under_assignment(assignment)
    result = ((pm_op(c1))(c2)).reduce_all()
    return BinaryComposite(t[0], t[1], result, source=t)

#TODO provide a correct version of a direct implementation of PM...
def tree_pm_fun_wrong(t, assignment=None):
    """H&K predicate modification -- restricted to type <et>.

    Note that this is the wrong way to implement this.  It does not properly handle variable renaming.  It is left here
    as a lesson in how not to do PM...
    """
    ts = meta.get_type_system()
    if not (ts.eq_check(t[0].type, type_property) and 
            ts.eq_check(t[1].type, type_property)):
        raise TypeMismatch(t[0], t[1], "Predicate Modification")
    try:
        # a convenience: try to keep the variable name the same as at least one of the functions.
        # this is the only part of this implementation that references the internals of the daughter nodes.
        varname = t[0].content.varname
    except AttributeError:
        # will be raised when t[0] is a PlaceholderTerm.
        varname = "x" # will this cause problems?
        # could just do "x" absolutely??
    c1 = t[0].content.under_assignment(assignment)
    c2 = t[1].content.under_assignment(assignment)
    print(c1, c2)
    body1 = c1.apply(meta.TypedTerm(varname, types.type_e))
    body2 = c2.apply(meta.TypedTerm(varname, types.type_e))
    conjoined_c = meta.LFun(type_e, body1 & body2, varname)
    return BinaryComposite(t[0], t[1], conjoined_c, source=t)


def tree_pa_metalanguage_fun(t, assignment=None):
    """H&K-style Predicate Abstraction, implemented in the metalanguage.

    This shifts the assignment for the interpretation of the sister of the binder to match up traces with the bound variable.
    It assumes the binder is the left sister, and will generate a TypeMismatch otherwise."""
    binder = t[0]
    if (binder.content is not None) or not binder.name.strip().isnumeric():
        raise types.TypeMismatch(t, None, "Predicate Abstraction")
    index = int(binder.name.strip())
    vname = "t%i" % index
    outer_vname = t[1].content.find_safe_variable()
    new_a = Assignment(assignment)
    new_a.update({vname: te("%s_e" % outer_vname)})
    f = meta.LFun(types.type_e, t[1].content.under_assignment(new_a), varname=outer_vname)
    return BinaryComposite(t[0], t[1], f, source=t)

class Trace(Item):
    """An indexed trace of some specified type.

    This is a meta-language implementation of traces!  That is, a trace in the metalanguage is a variable `t` numbered by index."""
    def __init__(self, index, typ=None):
        if typ is None:
            typ = types.type_e
        if index > 0:
            name = "t%i" % index
        else:
            name = "t"
        # Item constructor will set self.index
        Item.__init__(self, name, meta.TypedTerm(name, typ), index=index)        

class Binder(Item):
    """An indexed binder.  Note that its content is always `None`.  Currently untyped; this may change."""
    def __init__(self, index):
        Item.__init__(self, "%i" % index, None, index=index)

def pa_fun(binder, content, assignment=None):
    """Do predicate abstraction given a `binder` and `content`.

    This is a direct implementation.  Will find a (completely) unused variable name to abstract over, and replace
    any traces of the appropriate index with that variable.  This assumes a meta-language implementation of traces!"""
    if (binder.content is not None) or not binder.name.strip().isnumeric():
        raise TypeMismatch(binder, content, "Predicate Abstraction")
    index = int(binder.name.strip())
    vname = "t%i" % index
    # there could be more natural ways to do this...should H&K assignment functions be implemented directly?
    outer_vname = "x"
    inner_fun = meta.LFun(types.type_e, content.content.under_assignment(assignment), vname)
    used_variables = inner_fun.free_variables() | inner_fun.bound_variables() # totally brute force...
    outer_vname = meta.alpha_variant(outer_vname, used_variables)
    f = meta.LFun(types.type_e, (inner_fun)(outer_vname + "_e").reduce(), outer_vname)
    return BinaryComposite(binder, content, f)

# TODO: this is the same as tree_fa_fun_abstract, basically...
def fa_fun(fun, arg, assignment=None):
    """Do function application, given some function and argument."""
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(fun, arg):
        raise TypeMismatch(fun, arg, "Function Application")
    return BinaryComposite(fun, arg, 
                (fun.content.under_assignment(assignment)(arg.content.under_assignment(assignment))).reduce())

def pm_fun(fun1, fun2, assignment=None):
    """H&K predicate modification, given two functions.  Restricted to type <et>.

    This is implemented using the combinator `lang.pm_op`."""
    ts = meta.get_type_system()
    if not (ts.eq_check(fun1.type, type_property) and 
            ts.eq_check(fun2.type, type_property)):
        raise TypeMismatch(fun1, fun2, "Predicate Modification") # this isn't strictly necessary, but will make errors look slightly nicer.
    varname = fun1.content.varname
    c1 = fun1.content.under_assignment(assignment)
    c2 = fun2.content.under_assignment(assignment)
    result = ((pm_op(c1))(c2)).reduce_all()
    return BinaryComposite(fun1, fun2, result)






def setup_type_driven():
    """Build a basic bottom-up composition system with PM, FA, and PA.

    The composition system is set to `lang.td_system`.  It's recommended that you copy this rather than modifying it directly.  This 
    is the default composition system.

    Also exports a few basic lexical entries for testing purposes."""
    global td_system, cat, gray, john, pm, fa, pa, inP, texas, isV, julius
    # note that PM is only commutative if the underlying logic has commutative conjunction...
    oldlevel = meta.logger.level
    meta.logger.setLevel(logging.WARNING)
    pm = BinaryCompositionOp("PM", pm_fun, commutative=True, reduce=True)
    fa = BinaryCompositionOp("FA", fa_fun, reduce=True)
    pa = BinaryCompositionOp("PA", pa_fun, allow_none=True)
    td_system = CompositionSystem(rules=[fa, pm, pa], basictypes={type_e, type_t}, name="H&K simple")
    cat = Item("cat", "L x_e: Cat(x)")
    gray = Item("gray", "L x_e: Gray(x)")
    john = Item("John", "John_e")
    julius = Item("Julius", "Julius_e")
    inP = Item("in", "L x: L y: In(y)(x)")
    texas = Item("Texas", "Texas_e")
    pvar = meta.TypedTerm("p", types.type_property)
    isV = Item("is", meta.LFun(types.type_property, pvar, "p"))
    td_system.add_items(cat, gray, john, julius, inP, texas, isV)
    set_system(td_system)
    meta.logger.setLevel(oldlevel)

setup_type_driven()

def setup_hk_chap3():
    """Build a basic tree composition system modeled after chapter 3 of Heim and Kratzer.  This has just FA and PM.

    The composition system is set to `lang.hk3_system`.  It's recommended that you copy this rather than modifying it directly.

    Note that the lexical items defined by `setup_type_driven` can be used here too, and are in fact added to the lexicon of this system by default."""
    global hk3_system, tfa_l, tfa_r, tpm

    tfa_l = TreeCompositionOp("FA/left", tree_left_fa_fun) # Function Application
    tfa_r = TreeCompositionOp("FA/right", tree_right_fa_fun) # Function Application
    tpm = TreeCompositionOp("PM", tree_pm_fun) # Predicate Modification
    tpa = TreeCompositionOp("PA", tree_pa_metalanguage_fun, allow_none=True)
    nn = TreeCompositionOp("NN", tree_nn_fun, preconditions=tree_unary) # Non-branching Node

    hk3_system = TreeCompositionSystem(rules=[tfa_l, tfa_r, tpm, tpa, nn], basictypes={type_e, type_t}, name="H&K Tree version")
    hk3_system.add_items(cat, gray, john, julius, inP, texas, isV)


setup_hk_chap3()
