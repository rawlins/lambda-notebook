__all__ = ['composition', 'test']

# many things here are only exported to this namespace for backwards compatibility
from lamb.lang import composition
from lamb.lang.composition import set_system, get_system, CompositionSystem
from lamb.lang.composition import hk_system, td_system,  td_presup, compose
from lamb.lang.composition import hk3_system # backwards compatibility
from lamb.lang.composition import Item, Items, Composable, Binder, Trace, IndexedPronoun, PresupPronoun, Lexicon
from lamb.lang.composition import CompositionTree, AssignmentController
from lamb.lang.composition import UnaryCompositionOp, BinaryCompositionOp, TreeCompositionOp
from lamb.lang.composition import fa_fun, pa_fun, pm_fun, unary_factory, binary_factory, binary_factory_uncurried
