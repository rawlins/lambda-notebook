from lamb import utils
try:
    # for now, fail silently if this doesn't work.
    import svgling
    import svgling.html
except:
    pass

import copy, enum
from xml.etree import ElementTree
Element = ElementTree.Element
SubElement = ElementTree.SubElement

def log_warning(m):
    from lamb import meta
    meta.logger.warning(m)

class Direction(enum.Enum):
    TD = 0
    LR = 1

class DerivStyle(enum.Enum):
    BOXES = "boxes"
    PROOF = "proof"
    TREE = "tree"

def default(**kwargs):
    global default_default
    default_default = dict(default_default, **kwargs)

def reset_default():
    global default_default
    default_default = dict(style=DerivStyle.BOXES)

reset_default()

def merge_dicts(target, defaults):
    """Merge default styles from `defaults` into `target`.
    
    returns the merged dict.  (Leaves `target` untouched.)"""
    if target is None:
        target = dict()
    else:
        target = dict(target)
    if defaults is None:
        defaults = dict()
    for x in defaults:
        target.setdefault(x, defaults[x])
    return target

def merge_styles(target, defaults):
    global default_default
    if isinstance(target, DerivStyle):
        target = {"style": target}
    return merge_dicts(target, merge_dicts(defaults, default_default))

def element_with_text(name, text="", **kwargs):
    e = Element(name, **kwargs)
    e.text = text
    return e

def subelement_with_text(parent, name, text="", **kwargs):
    e = Element(name, **kwargs)
    e.text = text
    parent.append(e)
    return e

def elem_join(parent, j, l):
    if len(l) == 0:
        return
    for i in range(len(l) - 1):
        parent.append(l[i])
        parent.append(copy.deepcopy(j))
    parent.append(l[-1])
    return parent

def html_text_wrap(t):
    """The idea is that this is a safe wrapper for putting a string into an
    html output somewhere. It's a bit convoluted, because of attempting to
    work around various things that produce bad line breaking in mathjax
    rendering."""
    e = Element("div", style="display:inline-block;")
    subelement_with_text(e, "span", text=t)
    return e

def alert_span(t):
    return element_with_text("span", text=t, style="color:red;")

def to_html(x, style=None):
    if isinstance(x, str):
        return html_text_wrap(x)
    elif isinstance(x, Element):
        return x
    if style is None:
        style = dict()
    try:
        return x.render(**style)
    except:
        try:
            return ElementTree.fromstring(x._repr_html_())
        except:
            try:
                return html_text_wrap(x._repr_latex_())
            except:
                return html_text_wrap(repr(x))

def equality_table(lines):
    e = Element("table", style="margin:0px;")
    i = 0
    for l in lines:
        row = SubElement(e, "tr")
        if i > 0:
            first_cell = " $=$ "
        else:
            first_cell = ""
        subelement_with_text(row, "td", text=first_cell,
            style="padding-right:5px")
        l_cell = SubElement(row, "td", align="left", style="text-align:left;")
        l_cell.append(to_html(l))
        i += 1
    return e

def alternative_explanation(expl_str, alternative_str):
    # TODO: this version tends towards linebreaks in very wide tables
    e = Element("div", style="display: inline-block;")
    e.append(to_html(expl_str))
    e.append(element_with_text("span", " (or: " + alternative_str + ")",
                                                style="font-size:x-small;"))
    return e

class DisplayNode(object):
    def __init__(self, content=None, explanation=None, parts=None, style=None):
        if parts is None:
            parts = list()
        self.content = content
        self.explanation = explanation
        self.parts = parts
        self.style = style

    def render(self, **kwargs):
        return self.style.render(self.content, self.explanation, self.parts,
                                                                    **kwargs)

    def build_tree(self, **kwargs):
        # this may throw an exception if the style doesn't support build_tree
        return self.style.build_tree(self.content, self.explanation, self.parts,
                                                                    **kwargs)

    def _repr_html_(self):
        return ElementTree.tostring(self.render(), encoding="unicode",
                                                   method="html")

    def __repr__(self):
        # this is to avoid a unique object identifier showing up in
        # notebooks in text/plain output, creating meaningless differences
        return self.__class__.__name__ + " instance: HTML rendering only"

class Styled(object):
    def __init__(self, style=None):
        global default_default
        if style is None:
            style = dict()
        self.style = dict(default_default, **style)
    
    def get_style(self, kwargs, key, default):
        """Get the style named by `key`, if any; returns default if it can't be
        found.
        
        Uses the object's stored style, and kwargs; the latter overrides the
        stored style."""
        if not kwargs:
            return self.style.get(key, default)
        if key in kwargs:
            return kwargs.get(key)
        elif key in self.style:
            return self.style.get(key)
        else:
            return default   

    def __repr__(self):
        # this is to avoid a unique object identifier showing up in
        # notebooks in text/plain output, creating meaningless differences
        return self.__class__.__name__ + " instance: HTML rendering only"

class HTMLNodeDisplay(Styled):
    def __init__(self, **style):
        super().__init__(style=style)

    def render_content(self, c, **kwargs):
        if c is not None:
            return to_html(c, style=kwargs)
        else:
            return to_html("")

    def border_style(self, **kwargs):
        if self.get_style(kwargs, "border", True):
            return "border: 1px solid #848482;"
        else:
            return ""

    def padding_style(self, **kwargs):
        padding = {"padding-left": None,
                   "padding-right": None,
                   "padding-top": None,
                   "padding-bottom": None}
        lr_padding = self.get_style(kwargs, "lr-padding", "")
        all_padding = self.get_style(kwargs, "padding", "5px")
        s = ""
        if all_padding:
            padding = {k: all_padding for k in padding}
        if lr_padding:
            padding["padding-left"] = lr_padding
            padding["padding-right"] = lr_padding
        return "".join([("%s:%s;" % (k, padding[k]))
                                            for k in padding if padding[k]])

    def display_style(self, **kwargs):
        direct = self.get_style(kwargs, "direction", None)
        if direct == Direction.TD:
            return "display: block;"
        elif direct == Direction.LR:
            return "display: inline-block;"
        else:
            return ""

    def vertical_divs(self, lines, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", style="display:table;table-layout:auto;",
                                                                align=align)
        for l in lines:
            row = SubElement(e, "div", style="display:table-row;",)
            if isinstance(l, str) or isinstance(l, Element):
                l = [l]
            else:
                try:
                    iter(l)
                except:
                    l = [l]
            for c in l:
                cell = SubElement(row, "div",
                    style="display:table-cell;padding-right:2px; padding-left:2px;",
                    align=align)
                cell.append(to_html(c, style=kwargs))
        return e

    def horiz_divs(self, lines, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", style="display:table;")
        for l in lines:
            row = SubElement(e, "div", style="display:table-cell;", align=align)
            row.append(to_html(l, style=kwargs))
            # TODO: implement l as an iterable?
        return e

    def direction_divs(self, lines, **kwargs):
        direction = self.get_style(kwargs, "direction", Direction.TD)
        if direction == Direction.TD:
            return self.vertical_divs(lines, **kwargs)
        else:
            return self.horiz_divs(lines, **kwargs)

    def render_explanation(self, explanation, **kwargs):
        color = self.get_style(kwargs, "expl_color", "blue")
        if explanation is not None:
            expl = to_html(explanation, style=kwargs)
            e = Element("div", style=("white-space:nowrap; color:%s;" % color))
            if self.get_style(kwargs, "expl_style", "default") == "bracket":
                bold = SubElement(e, "b")
                bold.text = "["
                expl.tail = "]"
                bold.append(expl)
            else:
                e.append(expl)
            return e
        else:
            return to_html("")

    def render_parts(self, parts, **kwargs):
        if len(parts) == 1 and not isinstance(parts[0], list):
            return to_html(parts[0], style=kwargs)
        else:
            return self.direction_divs(parts, **kwargs)

    def render(self, content, explanation, parts, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", align=align,
            style=("display:block;"
                   + self.border_style(**kwargs)
                   + self.padding_style(**kwargs)))
        node_parts = list()
        if content is not None:
            node_parts.append(self.render_content(content, **kwargs))
        if explanation is not None:
            node_parts.append(self.render_explanation(explanation, **kwargs))
        if len(parts):
            node_parts.append(self.render_parts(parts, **kwargs))
        if len(node_parts) == 1:
            e.append(node_parts[0])
        elif len(node_parts) > 1:
            e.append(self.direction_divs(node_parts, **kwargs))
        return e

class TDBoxDisplay(HTMLNodeDisplay):
    def __init__(self, **style):
        style["border"] = True
        style["direction"] = Direction.LR
        style["align"] = "center"
        super().__init__(**style)

    def render_parts(self, parts, **kwargs):
        part_cells = list()
        for p in parts:
            part_e = Element("div",
                style=("display:table-cell;vertical-align:middle;"
                       + self.padding_style(**kwargs)))
            part_e.append(to_html(p, style=kwargs))
            part_cells.append(part_e)
        e = Element("div", style="display: table;")
        join = Element("div",
            style="align: center; vertical-align: middle; display: table-cell;")
        join.append(element_with_text("span", text="*",
                        style=("padding:1em;")))
        elem_join(e, join, part_cells)
        return e

    def render(self, content, explanation, parts, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", align=align,
            style=("display:table; margin:5px; border-collapse: collapse;"
                   + self.border_style(**kwargs)))
        parts_row = SubElement(e, "div", align="center",
            style="display:table-row;border-bottom:1px solid #848482")
        parts_inter = SubElement(parts_row, "div",
            style="display:table-cell;vertical-align:middle;")
        parts_inter.append(self.render_parts(parts, **kwargs))
        if explanation is not None:
            expl_inter = SubElement(parts_row, "div",
                style="display:table-cell;vertical-align:middle;border-left:1px solid #848482;padding:0.5em")
            expl_inter.append(self.render_explanation(explanation, **kwargs))
        content_row = SubElement(e, "div", align="center",
            style=("display:table-row;"
                   + self.padding_style(**kwargs)))
        content_cell = SubElement(content_row, "div", align=align,
                                                style="display:table-cell;")
        content_cell.append(self.render_content(content, **kwargs))
        if explanation is not None:
            SubElement(content_row, "div", style="display:table-cell;")
        return e

class TDProofDisplay(HTMLNodeDisplay):
    def __init__(self, **style):
        style["border"] = False
        style["direction"] = Direction.LR
        super().__init__(**style)

    def render_parts(self, parts, **kwargs):
        part_cells = list()
        for p in parts:
            part_e = Element("div",
                style=("vertical-align:bottom;display:table-cell;"
                       + self.padding_style(**kwargs)))
            part_e.append(to_html(p, style=kwargs))
            part_cells.append(part_e)
        e = Element("div", style="display: table;")
        join = Element("div", style="display: table-cell; padding-left:4em;")
        elem_join(e, join, part_cells)
        return e

    def render_explanation(self, explanation, **kwargs):
        # TODO: this is duplicated only so that the transform can be applied,
        # is there a simpler way?
        color = self.get_style(kwargs, "expl_color", "blue")
        if explanation is not None:
            expl = to_html(explanation, style=kwargs)
            # align this div with the middle of the proof line
            e = Element("div", style=("color:%s;" % color
                + "transform: translateY(-1em); padding-left:0.5em;"))
            if self.get_style(kwargs, "expl_style", "default") == "bracket":
                bold = SubElement(e, "b")
                bold.text = "["
                expl.tail = "]"
                bold.append(expl)
            else:
                e.append(expl)
            return e
        else:
            return to_html("")

    def render(self, content, explanation, parts, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", align=align,
            style=("display:table;" + self.border_style(**kwargs)))
        parts_row = SubElement(e, "div", align="center",
            style="display:table-row;")
        parts_inter = SubElement(parts_row, "div",
            style="display:table-cell;table-layout:auto;vertical-align:bottom;border-bottom:1px solid #848482;")
        parts_inter.append(self.render_parts(parts, **kwargs))
        SubElement(parts_row, "div", style="display:table-cell;")
        if explanation is not None:
            # The elaborateness here and in render_explanation is to get the
            # explanation centered relative to the line. TODO: is this ok
            # across browsers?
            mid = SubElement(e, "div", style="display:table-row;")
            SubElement(mid, "div", style="display: table-cell;")
            expl_inter = SubElement(mid, "div",
                style="display:table-cell;vertical-align:middle;")
            expl_inter2 = SubElement(expl_inter, "div",
                style="vertical-align:middle;height:0px;overflow:visible")
            expl_inter2.append(self.render_explanation(explanation, **kwargs))

        content_inter = SubElement(e, "div", align="center",
            style=("display:table-row;"
                   + self.padding_style(**kwargs)))
        content_inter.append(self.render_content(content, align="center",
                                                                    **kwargs))
        SubElement(content_inter, "div", style="display: table-cell;")

        return e

class TreeNodeDisplay(HTMLNodeDisplay):
    def render_node(self, content, explanation, **kwargs):
        e = Element("div",
            style="display:grid;grid-template-columns:auto auto;"
                  + self.padding_style(**kwargs))
        kwargs["lr-padding"] = "0.5em"
        kwargs["padding"] = None
        expl_div = SubElement(e, "div",
            style="align-self:end;justify-self:right;")
        expl_e = self.render_explanation(explanation, **kwargs)
        expl_e.set("style", expl_e.get("style", "") + "padding-right:4px;")
        expl_div.append(expl_e)
        content_div = SubElement(e, "div",
            style="justify-self:left;")
        content_div.append(self.render_content(content, **kwargs))
        return e

    def tree_layout(self, content, explanation, parts, **kwargs):
        # turn the structure into a tree-structured list, as far as possible:
        tree = self.build_tree(content, explanation, parts, **kwargs)
        # build an svgling.html.DivTreeLayout object:
        # TODO: it would be nice to just be able to use the DivTreeLayout
        # object overall...
        return svgling.html.draw_tree(tree,
                            horiz_spacing=svgling.core.HorizSpacing.TEXT)

    def render(self, content, explanation, parts, **kwargs):
        return self.tree_layout(content, explanation, parts, **kwargs).render()

    def build_tree(self, content, explanation, parts, **kwargs):
        tree = [self.render_node(content, explanation, **kwargs)]
        for p in parts:
            try:
                tree.append(p.build_tree(**kwargs))
            except:
                tree.append(to_html(p, style=kwargs))
        return tree


class LRDerivationDisplay(HTMLNodeDisplay):
    def __init__(self, **style):
        style["border"] = False
        super().__init__(**style)

    def render_parts(self, parts, **kwargs):
        align = self.get_style(kwargs, "align", "center")
        e = Element("div", align=align,
            style="display:table;border-collapse:collapse;")

        inter_style = "display:table-row;border-bottom:1px solid #848482;"
        last_style = "display:table-row;"
        for i in range(len(parts)):
            if i < len(parts) - 1:
                row_style = inter_style
            else:
                row_style = last_style
            row = SubElement(e, "div", style=row_style)
            subelement_with_text(row, "div", text=("%2d. " % (i+1)),
                style="display:table-cell;padding-right:5px;vertical-align:bottom;")
            kwargs["parent_table"] = row
            result = to_html(parts[i], style=kwargs)
            if result is not row:
                # otherwise, the to_html call has already done the appending
                sub_cell = SubElement(row, "div",
                    style="display:table-cell; vertical-align:bottom;padding-left:5px;padding-right:5px;")
                sub_cell.append(result)
        return e

    def render(self, content, explanation, parts, parent_table=None, **kwargs):
        align = self.get_style(kwargs, "align", "left")
        if parent_table:
            e = parent_table
        else:
            e = Element("div", align=align,
                style=("display:table;" + self.border_style(**kwargs)))
        if content is not None:
            content_cell = SubElement(e, "div",
                style="display:table-cell;vertical-align:bottom;border-right:1px solid #848482;padding-right:5px;")
            content_cell.append(self.render_content(content, **kwargs))
        if explanation is not None or len(parts):
            expl_cell = SubElement(e, "div",
                style="display:table-cell;vertical-align:bottom;padding-left:5px;padding-right:5px;padding-top:0.5em")
            sub_table = SubElement(expl_cell, "div", style="display:table;")
            if explanation is not None:
                expl_row = SubElement(sub_table, "div",
                    style="display:table-row;")
                expl_row.append(self.render_explanation(explanation, **kwargs))
            if len(parts):
                parts_row = SubElement(sub_table, "div",
                    style="display:table-row;vertical-align:bottom;")
                parts_row.append(self.render_parts(parts, **kwargs))
        return e

class EqualityDisplay(HTMLNodeDisplay):
    def render(self, content, explanation, parts, parent_table=None, **kwargs):
        lines = list()
        if content is not None:
            lines.append(to_html(content))
        lines.extend([to_html(p) for p in parts])
        e = equality_table(lines)
        return e

def deriv_style(style):
    deriv_style = style.get("style", DerivStyle.BOXES)
    if (deriv_style == DerivStyle.PROOF):
        return TDProofDisplay(**style)
    elif deriv_style == DerivStyle.TREE:
        defs = {
            "lr-padding": None,
            "padding": None
        }
        return TreeNodeDisplay(**merge_styles(style, defs))
    else: # BOXES
        return TDBoxDisplay(**style)

def leaf_style(style):
    deriv_style = style.get("style", DerivStyle.BOXES)
    if deriv_style == DerivStyle.TREE:
        defs = {
            "definiendum": True,
            "lr-padding": "1em"
        }
        style = merge_styles(style, defs)
    return HTMLNodeDisplay(**style)

def internal_style(style):
    deriv_style = style.get("style", DerivStyle.BOXES)
    if deriv_style == DerivStyle.TREE:
        defs = {
            "definiendum": False
        }
        style = merge_styles(style, defs)
    return HTMLNodeDisplay(**style)
