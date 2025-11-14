import unittest, logging

import lamb
from lamb import parsing, meta, types
from . import composition
from lamb.meta import logger

parsing.errors_raise = True

# used across multiple tests
basic_testcases = [
    "||test1|| = L x_e : P_<e,t>(x)",
    "||test2|| = L f_<e,t> : L x_e : f(x)",
    "||test3|| = f_<X,Y>",
    "test4 = g_<e,t>",
    "||is amb|| = L f_<e,t> : f",
    "||is amb[*]|| = L x_e : L y_e : x <=> y",
    "||is amb[*]|| = L x_n : L y_n : x <=> y",
    "||is amb[0]|| = L f_<e,t> : L x_e : f(x)",
    "||Kyle|| = K_e",
    "test5_<Y,X> = L x_Z: x"
    ]

class LangParsingTest(unittest.TestCase):
    def setUp(self):
        meta.core.set_strict_type_parsing()

    def tearDown(self):
        # other tests may want this, but let them decide
        meta.core.set_strict_type_parsing(False)

    def test_parsing(self):
        # really basic stuff:
        state = dict()
        logger.setLevel(logging.WARNING)
        parsing.parse("\n".join(basic_testcases), state=state)
        logger.setLevel(logging.INFO)
        self.assertEqual(len(state), 7)
        self.assertEqual(state["test1"].content, meta.te("L x_e : P_<e,t>(x)"))
        self.assertEqual(state["test2"].content, meta.te("L f_<e,t> : L x_e : f(x)"))
        self.assertEqual(state["test3"].content, meta.te("f_<X,Y>"))        
        self.assertEqual(state["test4"], meta.te("g_<e,t>"))
        self.assertEqual(state["test5"], meta.te("λ x_X: x_X")) # not the point, but this is sensitive to polymorphic resolution order

def has_ipython_repr(o):
    # test for the existence of one of the relevant IPython reprs. This doesn't
    # test that _display_ipython_ actually does something, but it's assumed
    # that if it is defined at all on `o`, we are good.
    # note: we explicitly don't look for _repr_svg_() here. Many objects will
    # inherit this from nltk.Tree, but it shows the base Tree object as-is,
    # with no lambda notebook info.
    return ('_ipython_display_' in dir(o)
            # note: currently everything inherits _repr_html_() from Composable,
            # but it may be None or raise NotImplementedError
            or '_repr_html_' in dir(o) and o._repr_html_()
            or '_repr_latex_' in dir(o) and o._repr_latex_()
            or '_repr_markdown_' in dir(o) and o._repr_markdown_())


# this is far from exhaustive. TODO:
# * test all built in composition ops
# * test all composition systems (currently, this is just td_system)
# * test transforms
class LangTest(unittest.TestCase):
    def setUp(self):
        meta.core.set_strict_type_parsing()
        self.state = dict()
        logger.setLevel(logging.WARNING)
        parsing.parse("\n".join(basic_testcases), state=self.state)
        logger.setLevel(logging.INFO)

    def tearDown(self):
        # other tests may want this, but let them decide
        meta.core.set_strict_type_parsing(False)

    def test_basic(self):
        from .composition import Item
        # this doesn't do much, but will test that basic metalanguage things
        # are working in the `lang` context
        cat = Item("cat", "L x_e: Cat_<e,t>(x)")
        gray = Item("gray", "L x_e: Gray_<e,t>(x)")
        john = Item("John", "John_e")
        julius = Item("Julius", "Julius_e")
        inP = Item("in", "L x_e: L y_e: In_<e,<e,t>>(y)(x)")
        texas = Item("Texas", "Texas_e")
        pvar = meta.TypedTerm("p", types.type_property)
        isV = Item("is", meta.LFun(meta.TypedTerm("p", typ=types.type_property), pvar))
        system = composition.td_system.copy()
        system.add_items(cat, gray, john, julius, inP, texas, isV)


    def test_fa(self):
        r1_a = self.state['test1'] * self.state['test2']
        # test2 is an identity function, reduction should not actually change
        # anything:
        self.assertEqual(len(r1_a), 1)
        self.assertEqual(r1_a[0].content, self.state['test1'].content)
        r1_b = self.state['test2'] * self.state['test1']
        self.assertEqual(len(r1_b), 1)
        self.assertEqual(r1_a[0].content, r1_b[0].content)
        # assumption: variable types enabled
        r2 = self.state['test3'] * self.state['test2']
        # FA should be possible in either direction
        self.assertEqual(len(r2), 2)
        # (test output?)
        r3 = self.state['test2'] * self.state['test2']
        # should fail to compose:
        self.assertEqual(len(r3), 0)

    def test_amb(self):
        r1 = self.state['test1'] * self.state['is_amb']
        self.assertEqual(len(r1), 1)
        self.assertEqual(r1[0].content, self.state['test1'].content) # identify function

        r2 = self.state['Kyle'] * (self.state['is_amb'] * self.state['Kyle'])
        self.assertEqual(len(r2), 1)
        self.assertEqual(r2[0].content, True) # identify function

    def test_pm(self):
        r1 = self.state['test1'] * self.state['test1']
        # one result via PM:
        self.assertEqual(len(r1), 1)
        r2 = self.state['test1'] * self.state['test3']
        # two results, FA and PM:
        self.assertEqual(len(r2), 2)

    def compose(self):
        # some multi-step composition tests
        r1 = (self.state['test1'] * self.state['test2']) * self.state['test2']
        self.assertEqual(len(r1), 1)
        r2 = (self.state['test2'] * self.state['test2']) * self.state['test2']
        # should fail and also not crash:
        self.assertEqual(len(r1), 0)

    def test_repr(self):
        # In automated notebook testing, any exceptions in IPython repr calls
        # are swallowed. Therefore, we need to be a bit careful to test various
        # repr calls directly.

        # strictly speaking, this should go in meta.test?
        repr(self.state['test4'])
        self.state['test4']._repr_latex_()

        # TODO: test Items, test parsing output, test lexicon
        # test IPython.display calls?
        outs = [
            self.state['test1'],
            composition.Items([self.state['test1'], self.state['test2']]),
            self.state['test1'] * self.state['test2'], # one-step success
            self.state['test3'] * self.state['test2'], # one-step failure
            (self.state['test1'] * self.state['test2']) * self.state['test2'], # two-step success
            (self.state['test2'] * self.state['test2']) * self.state['test2'], # two-step failure
            ]
        for o in outs:
            # all of the tested objects should support at least one non-trivial
            # IPython repr. (Currently, we don't actually test that
            # _display_ipython_ does something...)
            self.assertTrue(has_ipython_repr(o),
                msg=f"Failed repr existence test on {o.__class__}")
            self.assertTrue(has_ipython_repr(o.show()),
                msg=f"Failed .show() repr existence test on {o.__class__}")
            # now run all the reprs to look for crashes
            repr(o),
            repr(o.show())
            str(o.show())
            o.show()._repr_latex_()
            o.show()._repr_html_()
            o.show()._repr_markdown_()

        # test Lexicon repr
        l = composition.Lexicon()
        self.assertTrue(has_ipython_repr(l),
            msg=f"Failed repr existence test on Lexicon")
        l._repr_markdown_()
        l.update(self.state)
        l._repr_markdown_()

