#!/usr/local/bin/python3
import collections

from lamb import utils, types, meta
from lamb.utils import *
from lamb.types import type_e, type_t, type_property, TypeMismatch
from lamb.meta import  TypedExpr, ensuremath, MiniLatex
from lamb import tree_mini
from lamb.tree_mini import Tree


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




def inbr(s):
    return "|\!|\\mathbf{\\text{" + s + "}}|\!|"
    # would be better, but doesn't work
    # return "|\\!|\\text{<b>" + s + "</b>}|\\!|"

def inbrs(s, super):
    return inbr(s) + "^{" + super + "}"

def mathjax_indent():
    return "&nbsp;&nbsp;&nbsp;&nbsp;"

latex_indent = mathjax_indent

class Lexicon(object):
    def __init__(self):
        self.items = dict()

#composition_system = None

def set_system(s):
    global composition_system
    composition_system = s

def get_system():
    global composition_system
    return composition_system

set_system(None)

class Composable(object):
    """Abstract mixin for objects that can be composed using a composition system; provides * and **.
    """

    # def __iter__(self):
    #     raise NotImplementedError

    # def __len__(self):
    #     raise NotImplementedError

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
        # if other is None:
        #     return cs.compose_iterables(self)
        # else:
        #     if not (isinstance(other, Composable)):
        #         raise NotImplementedError
        # return cs.compose_iterables(self, other)
        #return self * other

    #@property
    #def content(self):
    #    raise NotImplementedError

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

    def _repr_latex_(self):
        return self.latex_str()

    def latex_str(self):
        raise NotImplementedError

    def latex_step_tree(self, derivations=False):
        return meta.MiniLatex(self.latex_step_tree_r(derivations=derivations))

    def latex_step_tree_r(self, derivations=False):
        raise NotImplementedError(repr(self))

    def __mul__(self, other):
        return self.compose(other)

    def __pow__(self, other):
        r = self * other
        if isinstance(r, CompositionResult):
            r.print_details()
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
            return ensuremath("{%s}^{%s}" % (self.base.latex_str(), ",".join([("%s/%s" % (self.store[k].latex_str(), k.latex_str())) for k in self.store.keys()])))
        else:
            return self.name # TODO: display defaults??


class AssignmentController(object):
    """This class is for managing the rendering and maintenance of specialized variables in the assignment function.

    For example, in many systems, index variables are notated as superscripts to the interpretation function.
    TODO: expand
    """
    def __init__(self, specials=[], reserved=None):
        self.specials = list(specials)
        self.reserved = {"index"}
        if reserved is not None:
            self.reserved = self.reserved | set(reserved)

    def validate(self, a):
        #for s in self.specials:
        #    if s not in a.keys():
        #        return False
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

class SingletonComposable(Composable):
    """A SingletonComposable stores one denotation ('content') in some form."""
    def __init__(self, content, system=None):
        if system is None:
            system = get_system()
        #if system is None:
        #    self.assign_controller = VacuousAssignmentController()
        #else:
        #    self.assign_controller = system.assign_controller
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

    def composite_name(self, other=None):
        if other is not None:
            return "[%s %s]" % (self.name, other.name)
        else:
            return "[%s]" % self.name

    def __repr__(self):
        return "||%s||%s = %s" % (self.name, self.assign_controller.render(latex=False), repr(self.content))

    def short_str(self, latex=False):
        if latex:
            return ensuremath(inbrs(self.name, self.assign_controller.render(latex=True)) + self.type_str_latex())
        else:
            return "||%s||" % self.name

    def type_str_latex(self):
        if self.type is None:
            return ""
        else:
            return "_{" + self.type.latex_str() + "}"

    def short_str_latex(self):
        #return ensuremath(inbr(self.name))
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

    # def __iter__(self):
    #     return iter((self,))

    def content_iter(self):
        return iter((self,))

    # def __len__(self):
    #     return 1


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
            #self.denotations = [denotation]
            raise NotImplementedError() # TODO use an Item?
        else:
            self.denotations = list(denotation) # requires iterable
            #raise NotImplementedError()

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
            if isinstance(self.node, str):
                placeholder = TreeComposite(content=PlaceholderTerm(self.node.lower(), self ,system=self.system), mode="Placeholder", source=self)
                self.denotations = [placeholder,]
                #self.placeholder=True
            else:
                raise NotImplementedError()


    def build_local_tree(self, override=True):
        """This function ensures that any necessary PlaceholderTerms are inserted into the denotation of a daughter node."""
        for i in range(len(self)):
            ch = self[i]
            if not isinstance(ch, CompositionTree):
                if isinstance(ch, str):
                    ch = CompositionTree(ch, system=self.system)
                    self[i] = ch
                elif isinstance(ch, Composable):
                    ch = CompositionTree.tree_factory(ch, system=self.system)
                elif isinstance(ch, Tree):
                    #ch = CompositionTree(ch.node, children=ch.children, system=self.system)
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

    def build_composite(self, den): # TODO: use a factory function
        return TreeComposite(*self.children, content=den, source=self)

    def build_perspective(self, *children):
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
        if isinstance(self.content, CompositionResult):
            for c in self.content:
                yield TreeComposite(*children, content=c, source=self)
        else:
            if self.content is None or len(self.content) == 0:
                # TODO: is this right?
                yield TreeComposite(*children, content=None, source=self)
            elif len(self.content) == 1:
                yield TreeComposite(*children, content=self.content[0], source=self)
            else:
                raise NotImplementedError()

    def locally_flat_iter(self): # TODO: generalize to n-ary trees
        """Return an iterator that yields TreeComposites for every possible denotation of the current node."""
        if len(self) == 0:
            yield from self.perspective_iter()
        elif len(self) == 1:
            if not isinstance(self[0], Composable):
                raise NotImplementedError("Cannot construct an iterator on non-Composables.  (Did compose_container get called without build_local_tree?)")
            for c in self[0].content_iter():
                yield from self.perspective_iter(self[0].build_composite(c))
        elif len(self) == 2:
            if not isinstance(self[0], Composable) or not isinstance(self[1], Composable):
                raise NotImplementedError("Cannot construct an iterator on non-Composables.  (Did compose_container get called without build_local_tree?)")
            for a in self[0].content_iter():
                for b in self[1].content_iter():
                    yield from self.perspective_iter(self[0].build_composite(a), self[1].build_composite(b))
        else:
            raise NotImplementedError()

    def find_empty_results(self):
        empty = list()
        for c in self:
            if isinstance(c.content, CompositionResult):
                if c.content.empty():
                    empty.append(c.content)
        #print(repr(empty))
        return empty

    def short_str(self, latex=False, children=True):
        if isinstance(self.node, str):
            n = self.node
        elif isinstance(self.node, SingletonComposable):
            n = self.node.short_str(latex=latex)
        else:
            n = str(self.node)
        c_list = []
        if children:
            for c in self.children:
                if isinstance(c, str):
                    c_list.append(c)
                elif isinstance(c, CompositionTree):
                    c_list.append(c.short_str(latex=latex, children=False))
                elif isinstance(c, Tree):
                    c_list.append(str(c.node))
                else:
                    c_list.append(str(c))
        if len(c_list) == 0:
            return "[%s]" % n
        else:
            return "[%s %s]" % (n, " ".join(c_list))

    def latex_str(self):
        if self.content is None:
            return Tree._repr_latex_(self)
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

    def _repr_latex_(self):
        return self.latex_str()

    def print_ipython_mathjax(self):
        return self.latex_step_tree()

    def latex_step_tree(self,derivations=False):
        if self.content is None:
            return Tree.print_ipython_mathjax(self)
        elif isinstance(self.content, CompositionResult):
            return self.content.latex_step_tree(derivations=derivations)
        elif len(self.content) == 1:
            return self.content[0].latex_step_tree(derivations=derivations)
        else:
            raise NotImplementedError()

    def __mul__(self, other):
        Composable.__mul__(self, other)

    @classmethod
    def from_tree(cls, t, system=None):
        return CompositionTree(t.node, t, system=system)

    def latex_step_tree_r(self, derivations=False):
        if len(self.content) == 1:
            return self.content[0].latex_step_tree_r(derivations=derivations)
        else:
            raise NotImplementedError(repr(self))

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
            t = Tree(composable)
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
                        print("Warning: Unknown source '%s' when converting a TreeComposite to a CompositionTree" % repr(composable.source))
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
                return str(self.source.node)
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
            #print(content.__class__)
            #print(content.content.__class__)
            if mode is None:
                mode = content.mode
            content = content.content
        Composite.__init__(self, children, content, mode=mode, source=source)
        Tree.__init__(self, content, children)
        self.children = self # hack

    @property
    def p1(self):
        return self[0]

    @property
    def p2(self):
        return self[1]


    def placeholder(self):
        if self.content is not None and isinstance(self.content, PlaceholderTerm):
            return True
        return False


    # def compose_str_latex(self):
    #     if isinstance(self.content, Exception):
    #         return self.content.latex_str()
    #     else:
    #         combination = " * ".join([n.short_str_latex() for n in self])
    #         s = "%s leads to: %s" % (combination, self.latex_str())
    #         if self.mode is not None:
    #             s += " (by %s)" % self.mode.name
    #         return s

    def compose_str_latex(self):
        return self.compose_str(latex=True)

    def compose_str(self, latex=False):
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
        l = self.content.derivation.steps_sequence(latex=True)
        s = "<table>"
        for (step, reason) in l:
            s += "<tr><td style=\"padding-right:5px\"> $=$ </td><td style=\"align:center\">%s</td></tr>" % step
        s += "</table>"
        return s

    def latex_terminal_tree(self, derivations=False):
        if self.content is None:
            return "<table align=\"center\"><tr><td align=\"center\">%s</td></tr><tr><td align=\"center\"><i>N/A</i></td></tr></table>\n" % (self.short_str_latex())
        else:
            return self.local_latex_tree(derivations=derivations)
            #return "<table align=\"center\"><tr><td align=\"center\">%s</td></tr><tr><td align=\"center\">%s</td></tr></table>\n" % (self.short_str_latex(), ensuremath(self.content.latex_str()))


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
        #if mode:
        #    s += "<td style=\"vertical-align:center\" align=\"center\">&nbsp;&nbsp;<b>[via %s]</b></td>" % self.mode.name
        s += "</tr></table>\n"
        return s

    def latex_step_tree_r(self, derivations=False):
        #if len(self) == 0:
        #    return self.latex_terminal_tree(derivations=derivations)
        #"<div><div>%s</div><div>%s</div><hr /><br />\n<div>%s (%s)</div></div>\n" % (
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
        #<td style=\"vertical-align:bottom\">%s</td></tr></table>" % (self.p1.latex_step_tree_r(), self.p2.latex_step_tree_r())
        if self.mode is None:
            s += "</tr>"
        else:
            s += "<td style=\"vertical-align:bottom;padding-bottom:5px;padding-left:10px\"><b>[%s]</b></td></tr>" % self.mode.name
        s += "<tr style=\"border-top: 1px solid #848482\"><td align=\"center\">%s</td><td></td></tr></table>\n" % self.local_latex_tree(derivations=derivations)
        return s

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
                if isinstance(self.source.node, str):
                    return self.source.node
                else:
                    return repr(self.source.node)
            else:
                return self.source

    def _repr_latex_(self):
        # since this inherits from Tree, need to ensure that we don't inherit a monkey-patched _repr_latex_ from there.
        return self.latex_str()

class BinaryComposite(TreeComposite):
    def __init__(self, p1, p2, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, p2, content=content, mode=mode, source=source)

class UnaryComposite(TreeComposite):
    def __init__(self, p1, content, mode=None, source=None):
        TreeComposite.__init__(self, p1, content=content, mode=mode, source=source)

class CompositionResult(Composable):
    def __init__(self, items, results, failures, source=None):
        self.items = items
        self.results = results
        self.failures = failures
        self.source = source

    def __repr__(self):
        return "CompositionResult(results=%s, failures=%s)" % (self.results, self.failures)
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
                #s += "    '%s' * '%s' leads to '%s'\n" % (composite.p1.short_str(), composite.p2.short_str(), repr(composite))
                s += "    " + composite.compose_str()
        return s

    def latex_str(self):
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
            for composite in self.results:
                #TODO: newlines in mathjax??
                s += "\n<br />" + latex_indent() + composite.latex_str()
                #s += latex_indent() + "`%s' $*$ `%s' leads to `%s'\n" % (composite.p1.short_str_latex(), composite.p2.short_str_latex(), ensuremath(composite.latex_str()))
        return s

    def failures_str_latex(self):
        return self.failures_str(latex=True)

    def failures_str(self, latex=False):
        s = str()
        for f in self.failures:
            if isinstance(f, CompositionResult):
                #if self.source is None:
                s += "Inheriting composition failure.  "
                #else:
                #        s += ("Inheriting composition failure from %s. " % self.source.short_str(latex=latex))
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


    def full_trace_latex(self):
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
            steps = r.find_steps()
            step_i = 1
            if len(self.results) > 1:
                s += "Path %i<br />\n" % i
            for step in steps:
                s += latex_indent() + ("Step %i: " % step_i) + step.compose_str_latex() + "<br />\n"
                step_i += 1
            i += 1
        return meta.MiniLatex(s)

    def latex_step_tree(self, derivations=False):
        s = str()
        if len(self.results) == 0:
            return "No succesful composition paths."
        elif len(self.results) == 1:
            s += "1 composition path:<br />"
        else:
            s += "%i composition paths:<br />\n" % len(self.results)
        i = 1
        for r in self.results:
            if len(self.results) > 1:
                s += "Path %i:<br />\n" % i
            # this will return a MiniLatex-packaged string.
            rst = r.latex_step_tree(derivations=derivations)
            s += rst._repr_latex_() + "<br /><br />"
            i += 1
        return MiniLatex(s)

    def reduce_all(self):
        for i in range(len(self.results)):
            new_c = self.results[i].content.reduce_all()
            # TODO probably should copy
            self.results[i].content = new_c



    def print_details(self):
        # TODO better
        if self.items is None:
            print("composing iterables")
        else:
            print("composing '%s' * '%s'" % (self.items[0], self.items[1]))
        print(str(self))


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

    def extend(self, other):
        if not isinstance(other, CompositionResult):
            raise ValueError
        self.results.extend(other.results)
        self.failures.extend(other.failures)





class Item(TreeComposite):
    """This class represents a lexical item.  It is implemented as a TreeComposite without a daughter."""
    def __init__(self, ol_name, content, index=None, mode=None):
        TreeComposite.__init__(self, content=content, mode=mode)
        #self.content = TypedExpr.ensure_typed_expr(content)
        self.__node_name__ = ol_name
        if index is None:
            self.index = None
        else:
            if index > 0:
                self.index = index
            else:
                self.index = 0

    # def __init__(self, ol_name, content, index=None):
    #     SingletonComposable.__init__(self, content)
    #     #self.content = TypedExpr.ensure_typed_expr(content)
    #     self.name = ol_name
    #     if index is None:
    #         self.index = None
    #     else:
    #         if index > 0:
    #             self.index = index
    #         else:
    #             self.index = 0

    @property
    def constant(self):
        return not self.placeholder()

    def copy(self):
        return Item(self.name, self.content.copy(), self.index)

    def reduce_all(self):
        self.content = self.content.reduce_all()
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


class BinaryCompositionOp(object):
    def __init__(self, name, operation, commutative=False, composite_name=None, allow_none=False, system=None):
        self.operation = operation
        self.__name__ = name
        self.commutative = commutative
        self.allow_none = allow_none
        if composite_name is not None:
            self.composite_name = composite_name
        if system is not None:
            self.system = system

    @property
    def name(self):
        return self.__name__

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
        return result

class UnaryCompositionOp(object):
    def __init__(self, name, operation, composite_name=None, allow_none=False, system=None,typeshift=False):
        self.operation = operation
        self.__name__ = name
        self.allow_none = allow_none
        if composite_name is not None:
            self.composite_name = composite_name
        if system is not None:
            self.system = system
        self.typeshift = typeshift

    @property
    def name(self):
        return self.__name__

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
        return result


def tree_binary(t):
    return (len(t) == 2)

def tree_unary(t):
    return (len(t) == 1)

def tree_leaf(t):
    return (len(t) == 0)


class TreeCompositionOp(object):
    def __init__(self, name, operation, preconditions=None, commutative=False, allow_none=False, system=None):
        self.operation = operation
        self.__name__ = name
        self.commutative = commutative
        self.allow_none = allow_none
        if preconditions is None:
            self.preconditions = tree_binary
        else:
            self.preconditions = preconditions
        self.system = system # adding the rule to a system will set this, no need to pre-check
        # if system is not None:
        #     self.system = system
        # else:
        #     self.system = get_system()

    @property
    def name(self):
        return self.__name__

    @property
    def arity(self):
        return 1

    def composite_name(self, t):
        return t.node

    def __str__(self):
        return "Tree composition op '%s'" % self.name

    # seems like this can't be a class method because of reference to the composition system
    # classmethod

    def build_local_old(self, tree):
        """Convert an arbitrary Tree into a local tree where all children are Composables.

        Uses PlaceholderTerm for subtrees which are not yet composed.

        This function is idempotent."""
        children = list()
        for ch in tree:
            if isinstance(ch, SingletonComposable):
                children.append(ch)
            elif isinstance(ch, Tree):
                if isinstance(ch.node, str):
                    nodename = ch.node
                else:
                    nodename = ch.node.name # handle the case where the node is something complex
                print(nodename)
                placeholder = Item(nodename, PlaceholderTerm(ch.node.lower(), ch,system=self.system))
                children.append(placeholder)
            elif isinstance(ch, str):
                # try to look up in the lexicon
                # TOOD: make this more sophisticated
                if self.system is not None:
                    i = self.system.lookup(ch)
                    if len(i) == 1 and isinstance(i[0], Item):
                        placeholder = i[0]
                    else:
                        placeholder = Item(ch, PlaceholderTerm(ch.lower(), ch,system=self.system))
                else:
                    placeholder = Item(ch, PlaceholderTerm(ch.lower(), ch,system=self.system))
                children.append(placeholder)
            else:
                print("Odd child: %s" % ch)
                raise NotImplementedError
        return Tree(tree.node, children)

    def build_local(self, tree):
        if not isinstance(tree, CompositionTree):
            tree = CompositionTree.from_tree(tree)
        tree.build_local_tree(override=False)
        return tree

    def __call__(self, tree, assignment=None):
        test = self.preconditions(tree)
        if not test:
            #return None
            raise TypeMismatch(tree, None, mode="Failed preconditions for %s" % self.name)
        #result = self.operation(self.build_local(tree), assignment=assignment)
        result = self.operation(tree, assignment=assignment)
        result.mode = self
        return result


class LexiconOp(TreeCompositionOp):
    def __init__(self, system=None):
        TreeCompositionOp.__init__(self, "Lexicon", self.lookup, preconditions=tree_leaf, system=system)

    def lookup(self, t, assignment=None):
        name = t.node
        #assert(name is not None)
        den = self.system.lookup_item(name)
        if den is None:
            raise TypeMismatch(t, None, mode="No lexical entry for '%s' found." % name)
        #elif len(den) > 1:
        #    raise NotImplementedError()
        return den


class PlaceholderTerm(meta.TypedTerm):
    """This class represents a placeholder for some denotation  that is unknown or not yet composed.  The primary use
    is in incrementally doing top-down composition."""
    def __init__(self, varname, placeholder_for, system=None):
        meta.TypedTerm.__init__(self, varname, types.undetermined_type)
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
            return self.placeholder_for.node


    def latex_str(self):
        return ensuremath(inbrs(self.placeholder_name(), self.assign_controller.render(latex=True)) + "_{" + self.type.latex_str() + "}")

    def __repr__(self):
        return "||%s||%s" % (self.placeholder_name(), self.assign_controller.render(latex=False))

    def expand(self):
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
        return PlaceholderTerm(self.op, self.placeholder_for, system=self.system)





class CompositionSystem(object):
    """A CompositionSystem describes an overarching way of dealing with semantic composition, made up of composition
    rules/operations, types, and a lexicon."""
    def __init__(self, rules=None, basictypes = None, name=None, a_controller=None):
        self.rules = list()
        for r in rules:
            self.add_rule(r)

        if basictypes is None:
            self.basictypes = set()
        else:
            self.basictypes = basictypes
        self.name = name

        if a_controller is None:
            #self.assign_controller = AssignmentController()
            self.assign_controller = VacuousAssignmentController()
        else:
            self.assign_controller = a_controller

        self.typecache = set()
        self.lexicon = dict()

    def copy(self):
        new_sys = CompositionSystem(rules=self.rules, basictypes=self.basictypes, name=self.name, a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon
        return new_sys

    def add_rule(self, r):
        r.system = self
        self.rules.append(r)

    def hastype(self, t):
        if t in self.basictypes:
            return 1
        elif t in self.typecache:
            return 1

        try:
            if self.hastype(t.left) and self.hastype(t.right):
                self.typecache.add(t)
                return 1
            else:
                return 0
        except:
            #print "Unexpected error:", sys.exc_info()[0]
            return 0

    def __repr__(self):
        if self.name is None:
            return "Anonymous composition system"
        else:
            return "Composition system: " + self.name

    def lookup(self, *items):
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
        try:
            if i in self.lexicon:
                return self.lexicon[i]
            else:
                return None
        except TypeError:
            return None

    def add_item(self, i):
        self.lexicon[i.name] = i

    def add_items(self, *items):
        for i in items:
            self.add_item(i)

    def compose(self, *items, assignment=None):
        """Compose the items according to the system.  Each item may be a container object."""
        #return self.compose_raw(*items, assignment=assignment)
        #TODO __big change__ (?) make sure this works generally...
        return self.compose_iterables(*items, assignment=assignment)

    def compose_raw(self, *items, assignment=None):
        """Attempts to compose the provided items.  This is the 'raw' version not intended to be called directly, and 
        assumes that non-determinism is already taken care of.

        Brute force tries every composition rule and order of items.  Note that currently this not handle arities > 2.
        """
        results = list()
        failures = list()
        items = self.lookup(*items)
        arity = len(items)
        for mode in self.rules:
            if arity != mode.arity:
                #TODO: put something in failure list?
                continue
            if arity == 1:
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
                            result.c_name = order[0].node
                        else:
                            #print(order[0])
                            print(mode)
                            result.c_name = order[0].name
                    else:
                        result.c_name = mode.composite_name(items[0], items[1])
                    results.append(result)
                except TypeMismatch as e:
                    #print(e)
                    if arity == 1:
                        failures.append(Composite(order[0], e, mode=mode))
                    else:
                        failures.append(BinaryComposite(order[0], order[1], e, mode=mode))
                    continue
        return CompositionResult(items, results, failures)

    #def compose(self, i1, i2):
    #    return self.compose_long(i1, i2).result_items()

    def compose_iterables(self, t1, t2=None, assignment=None):
        iter1 = t1.content_iter()
        if t2 is None:
            iter2 = None
        else:
            iter2 = t2.content_iter()
        r = self.compose_iterators(iter1, iter2, assignment=assignment)
        return r

    def compose_iterators(self, iter1, iter2=None, assignment=None):
        r = CompositionResult(None, [],[])
        if iter2 is None:
            for i1 in iter1:
                r.extend(self.compose_raw(i1, assignment=assignment))
        else:
            for i1 in iter1:
                for i2 in iter2:
                    r.extend(self.compose_raw(i1, i2, assignment=assignment))
        return r


    def compose_container(self, c, assignment=None):
        r = self.compose_iterators(c.locally_flat_iter(), assignment=assignment)
        #print("hi %s" % repr(r.failures))
        if r.empty() and len(r.failures) == 0:
            r.failures.extend(c.find_empty_results()) # find any errors inherited from subtrees.
        r.source = c
        return r

    def pcompose(self, i1, i2):
        cret = self.compose(i1,i2)
        cret.print_details()
        return cret


class TreeCompositionSystem(CompositionSystem):
    def __init__(self, rules=None, basictypes = None, name=None, a_controller=None):
        CompositionSystem.__init__(self, rules, basictypes, name, a_controller)
        self.add_rule(LexiconOp(system=self))

    def copy(self):
        new_sys = TreeCompositionSystem(rules=self.rules, basictypes=self.basictypes, name=self.name, a_controller=self.assign_controller)
        new_sys.lexicon = self.lexicon

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
        # TODO: rethink this
        if full_path is None:
            full_path = tuple()
        yield (tree, parent, path_from_par, full_path)
        if len_fun(tree) == 0:
            raise StopIteration()
        elif len_fun(tree) >= 1:
            for i in range(len_fun(tree)):
                yield from self.td_df_lr_gen(tree[i], tree, i, len_fun, full_path=full_path + (i,))
            #subgen = self.td_df_lr_gen(tree[0], tree, 0, len_fun)
            #for n in subgen:
            #    yield n
            # if len_fun(tree) == 2:
            #     yield from self.td_df_lr_gen(tree[1], tree, 1, len_fun)
            #     #subgen = self.td_df_lr_gen(tree[1], tree, 1, len_fun)
            #     #for n in subgen:
            #     #    yield n
            # else:
            #     raise NotImplementedError

    def tree_factory(self, composable):
        return CompositionTree.tree_factory(composable, system=self)

    def simple_composite_name(self, n1, n2):
        return "[%s %s]" % (n1, n2)

    def binary_tree_factory(self, c1, c2):
        t1 = self.tree_factory(c1)
        t2 = self.tree_factory(c2)
        return CompositionTree(self.simple_composite_name(t1.node, t2.node), children=[t1, t2], system=self)

    def compose(self, c1, c2=None, override=False, assignment=None):
        if c2 is None:
            tree = self.tree_factory(c1)
        else:
            tree = self.binary_tree_factory(c1, c2)
        #tree.build_local_tree(override=override)
        #return self.compose_container(tree)
        return tree.compose(assignment=assignment)

    def search_for_unexpanded(self, tree, search_gen, expanded_fun, len_fun):
        gen = search_gen(tree, None, None, len_fun)
        for (n, p, path, full_path) in gen:
            #print("recursing node '%s'" % n)
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
        if isinstance(node, CompositionResult):
            return len(node)
        if isinstance(node, Item):
            return 0

    def qsfu(self, tree):
        return self.search_for_unexpanded(tree, self.td_df_lr_gen, self.is_expanded, self.len_fun)

    def compose_path(self, root, path, assignment=None):
        if len(path) > 0:
            self.compose_path(root[path[0]], path[1:])
        #self.compose()
        return root.compose(override=True, assignment=assignment)

    def expand_next(self, tree):
        (subtree, parent, path_from_parent, full_path) = self.qsfu(tree)
        #expansion = subtree.content.expand()
        #expansion = subtree.compose()

        #parent[path_from_parent]
        #return self.compose(tree, override=True) # redo everything?
        self.compose_path(tree, full_path)

    def search_td_bf(self, node, expanded_fun, len_fun):
        if len_fun(node) == 0:
            return (None, )
        if len_fun(node) == 1:
            if expanded_fun(node):
                return (0,) + self.search_td_bf(self, node[0], expanded_fun, len_fun)
            else:
                return (None, )
        elif len_fun(node) == 2:
            if expanded_fun(node):
                if expanded_fun(node[0]):
                    if expanded_fun(node[1]):
                        return (0,) + self.search_td_bf(self, node[0], expanded_fun, len_fun)
            else:
                return (None, )

  








def te(s):
    return meta.TypedExpr.factory(s)

def tp(s):
    ts = meta.get_type_system()
    result = ts.type_parser(s)
    return result


def tree_fa_fun_abstract(f, a, assignment=None):
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(f, a):
        return None
    result = (f.content.under_assignment(assignment))(a.content.under_assignment(assignment))
    if not a.type.undetermined:
        result = result.reduce()
    return result

def tree_left_fa_fun(t, assignment=None):
    result = tree_fa_fun_abstract(t[0], t[1], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/left")
    return BinaryComposite(t[0], t[1], result, source=t)

def tree_right_fa_fun(t, assignment=None):
    result = tree_fa_fun_abstract(t[1], t[0], assignment)
    if result is None:
        raise TypeMismatch(t[0], t[1], "FA/right")
    return BinaryComposite(t[0], t[1], result, source=t)

    
#def tree_right_fa_fun(t, assignment=None):
#    if not types.UndeterminedType.fun_arg_ok(t[1], t[0]):
#        raise TypeMismatch(t[1], t[0], "FA/right")
#    result = (t[1].content.under_assignment(assignment)(t[0].content.under_assignment(assignment)))
#    if not t[0].type.undetermined:
#        result = result.reduce()
#    return BinaryComposite(t[1], t[0], result, source=t)

pm_op = te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")

def tree_pm_fun(t, assignment=None):
    """H&K predicate modification -- restricted to type <et>.

    This implementation uses the above function to perform PM via function application.
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
    # TODO: does this overgenerate uncertainty?
    if body1.type.undetermined or body2.type.undetermined:
        conjoined_c.type = types.UndeterminedType(conjoined_c.type)

    #varname = t[0].content.varname
    #c1 = t[0].content.under_assignment(assignment)
    #c2 = t[1].content.under_assignment(assignment)
    #if c2.varname != varname:
        # ensure that the two functions use the same variable name, by beta reduction
        #body2 = LFun(fun2.argtype, beta_reduce(fun2.body, fun2.varname, TypedTerm(varname, fun2.argtype)))
        # actually direct beta reduction isn't a good idea, because I'd have to ensure alpha conversion
        # so just apply with a new variable to get a body
    #    body2 = c2.apply(meta.TypedTerm(varname, c2.argtype))
    #else:
        # not sure this efficiency is really necessary
    #    body2 = c2.body
    #conjoined_c = meta.LFun(c1.argtype, c1.body & body2, c1.varname)
    return BinaryComposite(t[0], t[1], conjoined_c, source=t)




class Trace(Item):
    def __init__(self, index, typ=None):
        if typ is None:
            typ = types.type_e
        if index > 0:
            name = "t%i" % index
        else:
            name = "t"
        # Item constructor will set self.index
        Item.__init__(self, name, meta.TypedTerm(name, typ), index=index)        

def pa_fun(binder, content, assignment=None):
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

def fa_fun(fun, arg, assignment=None):
    ts = meta.get_type_system()
    if not ts.fun_arg_check_bool(fun, arg):
        raise TypeMismatch(fun, arg, "Function Application")
    #if (not fun.type.functional()) or fun.type.left != arg.type:
    #    raise TypeMismatch(fun, arg, "Function Application")
    return BinaryComposite(fun, arg, 
                (fun.content.under_assignment(assignment)(arg.content.under_assignment(assignment))).reduce())

def pm_fun(fun1, fun2, assignment=None):
    """H&K predicate modification -- restricted to type <et>."""
    ts = meta.get_type_system()
    if not (ts.eq_check(fun1.type, type_property) and 
            ts.eq_check(fun2.type, type_property)):
        raise TypeMismatch(fun1, fun2, "Predicate Modification")
    #if fun1.type != fun2.type or fun1.type != type_property:
    #    raise TypeMismatch(fun1, fun2, "Predicate Modification")
    varname = fun1.content.varname
    c1 = fun1.content.under_assignment(assignment)
    c2 = fun2.content.under_assignment(assignment)
    if c2.varname != varname:
        # ensure that the two functions use the same variable name, by beta reduction
        #body2 = LFun(fun2.argtype, beta_reduce(fun2.body, fun2.varname, TypedTerm(varname, fun2.argtype)))
        # actually direct beta reduction isn't a good idea, because I'd have to ensure alpha conversion
        # so just apply with a new variable to get a body
        body2 = c2.apply(meta.TypedTerm(varname, c2.argtype))
    else:
        # not sure this efficiency is really necessary
        body2 = c2.body
    conjoined_c = meta.LFun(c1.argtype, c1.body & body2, c1.varname)
    return BinaryComposite(fun1, fun2, conjoined_c)


def setup_type_driven():
    global td_system, cat, gray, john, pm, fa, pa, inP, texas, isV, julius
    # note that PM is only commutative if the underlying logic has commutative conjunction...
    pm = BinaryCompositionOp("PM", pm_fun, commutative=False)
    fa = BinaryCompositionOp("FA", fa_fun)
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

setup_type_driven()

def setup_hk_chap3():
    global hk3_system, tfa_l, tfa_r, tpm

    tfa_l = TreeCompositionOp("FA/left", tree_left_fa_fun)
    tfa_r = TreeCompositionOp("FA/right", tree_right_fa_fun)
    tpm = TreeCompositionOp("PM", tree_pm_fun)

    hk3_system = TreeCompositionSystem(rules=[tfa_l, tfa_r, tpm], basictypes={type_e, type_t}, name="H&K Tree version")
    hk3_system.add_items(cat, gray, john, julius, inP, texas, isV)


setup_hk_chap3()
