from lamb import utils

def log_warning(m):
    from lamb import meta
    meta.logger.warning(m)



global td_box_style, td_proof_style, lr_num_style, lr_table_style, leaf_derivs_style

td_box_style = {"direction": "td", 
                "style": "boxes",
                "parts_style": "compose",
                "expl_style": "bracket", 
                "expl_color": "blue", 
                "leaf_align": "center",
                "leaf_style": "div"}

td_proof_style = {"direction": "td", 
                  "style": "proof",
                  "parts_style": "compose",
                  "expl_style": "bracket", 
                  "expl_color": "blue", 
                  "leaf_align": "center",
                  "leaf_style": "div"}

leaf_derivs_style = {"direction": "td", 
                     "style": "proof",
                     "parts_style": "eq",
                     "expl_style": "bracket", 
                     "expl_color": "blue", 
                     "leaf_align": "center",
                     "leaf_style": "div"}

lr_num_style = {"direction": "lr",
                "style": "boxes",
                "parts_style": "steps",
                "expl_style": "simple",
                "expl_color": "blue",
                "leaf_align": "left",
                "leaf_style": "div"}

lr_table_style = {"direction": "lr",
                  "style": "rows",
                  "parts_style": "steps",
                  "expl_style": "simple",
                  "expl_color": "blue",
                  "leaf_align": "left",
                  "leaf_style": "div"}

class Styled(object):
    def __init__(self, style=None):
        if style is None:
            self.style = dict()
        else:
            self.style = dict(style)
    
    def get_style(self, kwargs, key, default):
        """Get the style named by `key`, if any; returns default if it can't be found.
        
        Uses the objects stored style, and kwargs; the latter overrides the stored style."""
        if not kwargs:
            return self.style.get(key, default)
        if key in kwargs:
            return kwargs.get(key)
        elif key in self.style:
            return self.style.get(key)
        else:
            return default   

    @classmethod
    def merge_styles(cls, target, defaults):
        """Merge default styles from `defaults` into `target`.
        
        returns the merged dict.  (Leaves `target` untouched.)"""
        if not target:
            target = dict()
        else:
            target = dict(target)
        if not defaults:
            defaults = dict()
        for x in defaults:
            target.setdefault(x, defaults[x])
        return target
        
    @classmethod
    def to_str(cls, x, style=None):
        if isinstance(x, str):
            return x
        try:
            if style is None:
                return x.html_render()
            else:
                return x.html_render(**style)
        except:
            try:
                return x._repr_latex_()
            except:
                return repr(x)

class RecursiveDerivationDisplay(Styled):
    """Class for rendering some recursive (tree-structured) data.
    
    Each node has two parts, the content, and an "explanation".  (E.g. in a derivation this is used to explain each step.)
    A node may have parts."""
    def __init__(self, content, explanation=None, parts=None, style=None):
        if parts is None:
            parts = list()
        self.content = content
        self.explanation = explanation
        self.parts = parts
        super().__init__(style=style)

        
    def render_expl_bracket(self, **kwargs):
        color = self.get_style(kwargs, "expl_color", "blue")
        if self.explanation:
            return "<span style=\"color:%s\"><b>[%s]</b></span>" % (color, self.to_str(self.explanation, style=kwargs))
        else:
            return ""
        
    def render_expl_simple(self, **kwargs):
        color = self.get_style(kwargs, "expl_color", "blue")
        if self.explanation:
            return "<span style=\"color:%s\">%s</span>" % (color, self.to_str(self.explanation, style=kwargs))
        else:
            return ""
            
    def render_expl(self, **kwargs):
        """Render the 'explanation' of the tree node.  Styles ('expl_style'):
        'simple': just a regular span.  (default)
        'bracket': in brackets and bold.
        
        the key 'expl_color' determines the color of the span.  Default is 'blue'."""
        style = self.get_style(kwargs, "expl_style", "default")
        if style == "default" or style == "simple":
            return self.render_expl_simple(**kwargs)
        elif style == "bracket":
            return self.render_expl_bracket(**kwargs)
        else:
            log_warning("Unknown style '%s'" % style)
            return self.render_expl_simple(**kwargs)
    
    def render_content(self, **kwargs):
        """Renders the content of the tree node."""
        mainstyle = self.get_style(kwargs, "style", "default")
        if not self.content:
            return ""
        if mainstyle == "rows":
            return "<td style=\"vertical-align:bottom;padding-right:10px\">%s</td>" % self.to_str(self.content, style=kwargs)
        else:
            return self.to_str(self.content, style=kwargs)
    
    def render_parts_table_compose(self, **kwargs):
        part_cells = []
        for p in self.parts:
            part_cells.append("<td style=\"vertical-align:bottom;padding:5px\">%s</td>" % self.to_str(p, style=kwargs))
        s = "<table><tr>"
        s += "<td style=\"vertical-align:bottom;padding:10px\">$\circ$</td>".join(part_cells)
        s += "</tr></table>"
        return s
    
    def render_parts_table_steps(self, **kwargs):
        part_cells = []
        i = 1
        for p in self.parts:
            if i < len(self.parts):
                part_cells.append("<tr style=\"border-bottom:1px solid #848482;padding-bottom:5px\"><td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td><td style=\"padding-left:10px;border-left:1px solid #848482;padding-bottom:3px\">%s</td></tr>" % (i, self.to_str(p, style=kwargs)))
            else:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td><td style=\"padding-left:10px;border-left:1px solid #848482;padding-bottom:3px\">%s</td></tr>" % (i, self.to_str(p, style=kwargs)))
            i += 1
        s = "<table style=\"padding-bottom:5px\">"
        s += "".join(part_cells)
        s += "</table>"
        return s

    def render_parts_eq_seq(self, **kwargs):
        part_cells = []
        i = 1
        for p in self.parts:
            if i == 1:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px\"></td><td style=\"align:left\">%s</td></tr>" % (self.to_str(p, style=kwargs)))
            else:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px\"> $=$ </td><td style=\"align:left\">%s</td></tr>" % (self.to_str(p, style=kwargs)))
            i += 1
        s = "<table style=\"padding-bottom:5px\">"
        s += "".join(part_cells)
        s += "</table>"
        return s

    def render_parts_table_steps_rows(self, **kwargs):
        part_cells = []
        i = 1
        for p in self.parts:
            if i < len(self.parts):
                part_cells.append("<tr style=\"border-bottom:1px solid #848482;padding-bottom:5px\"><td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td>%s</tr>" % (i, self.to_str(p, style=kwargs)))
            else:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px;vertical-align:bottom\">%2i. </td>%s</tr>" % (i, self.to_str(p, style=kwargs)))
            i += 1
        s = "<table style=\"padding-bottom:5px\">"
        s += "".join(part_cells)
        s += "</table>"
        return s
    
    def render_parts(self, **kwargs):
        """Renders the child nodes.  Styles ('parts_style'):
        'compose': horizontally chained with a mathjax open circle.
        'steps': each child in a numbered row.  This will react to the main style.
        """
        style = self.get_style(kwargs, "parts_style", "default")
        main_style = self.get_style(kwargs, "style", "default")
        if style == "default" or style == "compose":
            return self.render_parts_table_compose(**kwargs)
        elif style == "steps":
            if main_style == "rows":
                return self.render_parts_table_steps_rows(**kwargs)
            else:
                return self.render_parts_table_steps(**kwargs)
        elif style == "eq":
            return self.render_parts_eq_seq(**kwargs)
        else:
            log_warning("Unknown style '%s'" % style)
            return self.render_parts_table_steps(**kwargs)
        
    def terminal_render(self, **kwargs):
        return self.render_content(**kwargs)
         
    def nonterminal_render_proof(self, **kwargs):
        expl_loc = self.get_style(kwargs, "expl_loc", "above")
        above = expl_loc == "above"
        s = "<table><tr><td style=\"vertical-align:bottom;padding:0px 10px\" align=\"center\">"
        s += self.render_parts(**kwargs)
        s += "</td>"
        expl = self.render_expl(**kwargs)
        if above and len(expl) > 0:
            s += "<td style=\"border:1px solid #848482;vertical-align:center;padding:10px\">"
            s += expl
            s += "</td></tr>"
        else:
            s += "<td></td></tr>"
        #if len(expl) > 0:
        #    s += "<td style=\"vertical-align:bottom;padding-bottom:5px;padding-left:10px\">"
        #    s += expl
        #    s += "</td></tr>"
        #else:
        #    s += "</tr>"
        s += "<tr style=\"border-top: 1px solid #848482\"><td align=\"center\">%s</td>" % self.render_content(**kwargs)
        if (not above) and len(expl) > 0:
            s += "<td style=\"vertical-align:bottom;padding-bottom:5px;padding-left:10px\">"
            s += expl
            s += "</td></tr></table>\n"
        else:
            s += "<td></td></tr></table>\n"
        return s
    
    def nonterminal_render_td_boxes(self, **kwargs):
        expl_loc = self.get_style(kwargs, "expl_loc", "above")
        above = expl_loc == "above"
        s = "<table><tr style=\"border:1px solid #848482\"><td style=\"vertical-align:bottom;padding:0px 10px\" align=\"center\">"
        s += self.render_parts(**kwargs)
        s += "</td>"
        expl = self.render_expl(**kwargs)
        if above and len(expl) > 0:
            s += "<td style=\"border-left:1px solid #848482;vertical-align:center;padding:10px\">"
            s += expl
            s += "</td></tr>"
        else:
            s += "<td></td></tr>"
        s += "<tr style=\"border-style:solid;border-color:#848482;border-width:0px 1px 1px 1px\"><td style=\"padding:5px\" align=\"center\">%s</td>" % self.render_content(**kwargs)
        if ((not above) and len(expl) > 0):
            s += "<td style=\"border-top:1px solid #848482;vertical-align:center;padding:5px\">"
            s += expl
            s += "</td></tr></table>\n"
        else:
            s += "<td></td></tr></table>"
        return s
        
    def nonterminal_render_lr_boxes(self, **kwargs):
        expl = self.render_expl(**kwargs)
        s = "<table>"
        if len(expl) > 0 and len(self.parts) > 0:
            s += "<tr><td></td><td style=\"border-left:1px solid #848482\">%s</td></tr>" % expl
        s += "<tr><td style=\"vertical-align:bottom;padding-right:10px\">%s</td>" % self.render_content(**kwargs)
        if len(self.parts) > 0:
            s += "<td style=\"border: 1px solid #848482;vertical-align:bottom;padding:0px 10px\">"
            s += self.render_parts(**kwargs)
            s += "</td></tr>"
        else: # align explanation and content if there are no subparts
            s += "<td style=\"border-left:1px solid #848482\">%s</td></tr>" % expl
        
        #s += "<tr style=\"border-style:solid;border-color:#848482;border-width:0px 1px 1px 1px\"><td align=\"center\">%s</td>" % self.render_content()
#         if len(expl) > 0:
#             s += "<td style=\"vertical-align:bottom;padding-bottom:5px;padding-left:10px\">"
#             s += expl
#             s += "</td></tr></table>\n"
#         else:
#             s += "</tr></table>\n"
        s += "</table>"
        return s

    def nonterminal_render_lr_boxes_rows(self, **kwargs):
        expl = self.render_expl(**kwargs)
        s = self.render_content(**kwargs)
        s += "<td style=\"border-left:1px solid #848482\">"
        if len(self.parts) > 0:
            if len(expl) > 0:
                s += "<div>%s</div>" % expl
            #s = "<table>"
            #s += "<tr><td style=\"border-left:1px solid #848482\">%s</td></tr>" % expl
            s += "<div>%s</div>" % self.render_parts(**kwargs)
        else: # align explanation and content if there are no subparts
            s += expl
        s += "</td>"        
        return s
    
    def nonterminal_render(self, **kwargs):
        """
        Renders a non-terminal (or actually, a terminal under certain conditions).  This is the main function.  
        Responds to 'style' and 'direction'.  Direction is either 'lr' or 'td'.
        'proof': proof-tree style, 'td' direction only.
        'boxes': recursive boxes for each subtree.  In the 'td' direction this looks similar to a proof-tree, in the 'lr' direction it is a non-vertically-aligned version of 'rows'.
        'rows': each child in a numbered row; each row is _not_ self-contained but rather a sequence of '<td>'s.  Has the appearance of recursive tables.  Careful modifying this one, it's easy to get the html wrong which can produce unpredictable results. 'lr' only, may not work with all other styles.
        
        To use 'rows' you should just use 'lr_table_style'.  Unfortunately it looks nice, despite the annoying internal complexity.
        Note hack in `_repr_latex_` for this style.
        """
        style = self.get_style(kwargs, "style", "default")
        direction = self.get_style(kwargs, "direction", "td")
        if direction == "td" or direction == "default":
            if style == "boxes" or style == "default":
                return self.nonterminal_render_td_boxes(**kwargs)
            elif style == "proof":
                return self.nonterminal_render_proof(**kwargs)
            else:
                log_warning("Unknown td style '%s'" % style)
                return self.nonterminal_render_td_boxes(**kwargs)
        elif direction == "lr":
            if style == "boxes":
                return self.nonterminal_render_lr_boxes(**kwargs)
            elif style == "rows":
                return self.nonterminal_render_lr_boxes_rows(**kwargs)
            else:
                log_warning("Unknown lr style '%s'" % style)
                return self.nonterminal_render_lr_boxes(**kwargs)
        else:
            log_warning("Unknown direction '%s'" % direction)
            return self.nonterminal_render_td_boxes(**kwargs)
        
    def html_render(self, **kwargs):
        """Render the structure given some style specified by kwargs."""
        if len(self.parts) > 0 or self.explanation:
            return self.nonterminal_render(**kwargs)
        else:
            return self.terminal_render(**kwargs)
    
    def restyle(self, **kwargs):
        """Uses `kwargs` to override the stored style.  This displays the result; it does not actually modify `self`."""
        if self.get_style(kwargs, "style", "default") == "rows":
            out = "<table><tr>%s</tr></table>" % self.html_render(**kwargs)
        else:
            out = self.html_render(**kwargs)
        return utils.MiniLatex(out)
    
    def _repr_latex_(self):
        if self.get_style(None, "style", "default") == "rows":
            return "<table><tr>%s</tr></table>" % self.html_render()
        else:
            return self.html_render()
        
class RecursiveDerivationLeaf(Styled):
    """Class for leaf nodes.  Note that RecursiveDerivationDisplay can handle leaf nodes as well;
    this class is mainly intended for using a very different style."""
    def __init__(self, *parts, style=None):
        self.parts = parts
        super().__init__(style)
        
    def html_render(self, **kwargs):
        style = self.get_style(kwargs, "leaf_style", "div")
        if style == "div" or style == "default":
            return self.div_render(**kwargs)
        elif style == "table":
            return self.table_rows_render(**kwargs)
        elif style == "eq":
            return self.render_eq_seq(**kwargs)
        else:
            log_warning("Unknown style '%s'" % style)
            return self.div_render(**kwargs)
        
    def div_render(self, **kwargs):
        align = self.get_style(kwargs, "leaf_align", "center")
        if len(self.parts) == 0:
            return ""
        elif len(self.parts) == 1:
            return "<div style=\"margin-top:10px;vertical-align:bottom;text-align:%s\">%s</div>" % (align, self.to_str(self.parts[0], style=kwargs))
        else:
            s = "<div style=\"margin-top:10px\">"
            for p in self.parts:
                s += "<div style=\"vertical-align:bottom;text-align:%s\">%s</div>" % (align, self.to_str(p, style=kwargs))
            s += "</div>"
        return s

    def render_eq_seq(self, **kwargs):
        align = self.get_style(kwargs, "leaf_align", "center")
        if len(self.parts) == 0:
            return ""
        part_cells = []
        i = 1
        for p in self.parts:
            if i == 1:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px\"></td><td style=\"text-align:%s\">%s</td></tr>" % (align, self.to_str(p, style=kwargs)))
            else:
                part_cells.append("<tr style=\"padding-bottom:5px\"><td style=\"padding-right:5px\"> $=$ </td><td style=\"text-align:%s\">%s</td></tr>" % (align, self.to_str(p, style=kwargs)))
            i += 1
        s = "<table style=\"padding-bottom:5px\">"
        s += "".join(part_cells)
        s += "</table>"
        return s
        
    def table_rows_render(self, **kwargs):
        align = self.get_style(kwargs, "leaf_align", "center")
        if len(self.parts) == 0:
            return ""
        elif len(self.parts) == 1:
            return "<table style=\"margin-top:10px\"><tr><td style=\"vertical-align:bottom\" align=\"%s\">%s</td></tr></table>" % (align,self.to_str(self.parts[0], style=kwargs))
        else:
            s = "<table style=\"margin-top:10px\">"
            for p in self.parts:
                s += "<tr><td style=\"vertical-align:bottom\" align=\"%s\">%s</td></tr>" % (align,self.to_str(p, style=kwargs))
            s += "</table>"
        return s
    
    def _repr_latex_(self):
        return self.html_render()