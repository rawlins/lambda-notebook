__all__ = ['core', 'boolean', 'meta', 'number', 'sets']

# -*- coding: utf-8 -*-
from numbers import Number
from lamb import types, utils, parsing, display
from lamb.types import TypeMismatch, type_e, type_t, type_n
from lamb.types import type_property, type_transitive, BasicType, FunType
# from lamb.utils import *

from lamb.meta import boolean, number, sets, core
from lamb.meta.core import TypedExpr, TypedTerm, CustomTerm, ApplicationExpr
from lamb.meta.core import LFun, BindingOp
from lamb.meta.core import Tuple, TupleIndex, Partial, Disjunctive, BinaryGenericEqExpr
from lamb.meta.core import registry, logger, derived, Derivation, op, op_expr_factory
from lamb.meta.core import get_type_system, set_type_system, constants_use_custom, ts_unify, ts_compatible
from lamb.meta.core import te, tp, term, let_wrapper, check_type, MiniOp, typed_expr
from lamb.meta.core import geach_combinator, fun_compose, unify

from lamb.meta.boolean import true_term, false_term

from lamb.meta.meta import truthtable, truthtable_equiv, MetaTerm

###############
#
# Setup
#
###############

def default_metalanguage():
    registry.clear()
    registry.add_binding_op(LFun)
    boolean.setup_operators()
    number.setup_operators()
    sets.setup_operators()
    registry.add_operator(core.BinaryGenericEqExpr, None, None)

default_metalanguage()

# TODO, move all the tests into their own module?
def test_setup():
    global ident, ia, ib, P, Q, p, y, t, testf, body, pmw_test1, pmw_test1b, t2
    ident = te("L x_e : x")
    ia = TypedExpr.factory(ident, "y")
    ib = LFun(type_e, ia, "y")
    P = TypedTerm("P", FunType(type_e, type_t))
    Q = TypedTerm("Q", FunType(type_e, type_t))
    x = TypedTerm("x", type_e)
    y = TypedTerm("y", type_e)
    t = TypedExpr.factory(P, x)
    t2 = TypedExpr.factory(Q, x)
    body = TypedExpr.factory("&", t, t) | t
    p = TypedTerm("p", type_t)
    testf = LFun(type_e, body)

    pmw_test1 = LFun(type_t, LFun(type_e, t & p, "x"), "p")
    pmw_test1b = LFun(type_e, t & t2, "x")
    # test: when a free variable in a function scopes under an operator, do not
    # bind the variable on application
    assert pmw_test1.apply(t2) != pmw_test1b

    # Different version of the same test: direct variable substitution
    test2 = TypedExpr.factory("L y_e : L x_e : y_e")
    test2b = TypedExpr.factory("L x_e : x_e")
    assert test2.apply(x) != test2b

test_setup()
