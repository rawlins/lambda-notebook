__all__ = ['core', 'boolean', 'meta', 'number', 'ply', 'quantifiers', 'sets', 'test']

# -*- coding: utf-8 -*-
from numbers import Number
from lamb import types, utils, parsing, display
from lamb.types import TypeMismatch, type_e, type_t, type_n
from lamb.types import type_property, type_transitive, BasicType, FunType

from lamb.meta import core, boolean, meta, number, ply, quantifiers, sets, test
from lamb.meta.core import TypedExpr, TypedTerm, CustomTerm, ApplicationExpr
from lamb.meta.core import LFun, BindingOp
from lamb.meta.core import Tuple, TupleIndex, Partial, Disjunctive, BinaryGenericEqExpr
from lamb.meta.core import registry, logger, op, op_expr_factory
from lamb.meta.core import get_type_system, set_type_system, constants_use_custom, ts_unify, ts_compatible
from lamb.meta.core import te, is_te, tp, term, let_wrapper, check_type, MiniOp
from lamb.meta.core import unify, global_namespace

from lamb.meta.ply import simplify_all, derived, default_sopts, collect, join

from lamb.meta.boolean import true_term, false_term

from lamb.meta.meta import truthtable, truthtable_equiv, MetaTerm, Assignment, Model
from lamb.meta.meta import compiled, exec

###############
#
# Setup
#
###############

def default_metalanguage():
    registry.clear()
    registry.add_binding_op(LFun)
    for m in [boolean, number, sets, quantifiers]:
        m.setup_operators()
    registry.add_operator(core.BinaryGenericEqExpr, None, None)


def reset():
    core.reset()
    default_metalanguage()


default_metalanguage()

# TODO, move these tests elsewhere?
def test_setup():
    ident = te("L x_e : x")
    ia = TypedExpr.factory(ident, "y")
    ib = LFun('y', ia, vartype=type_e)
    P = TypedTerm("P", FunType(type_e, type_t))
    Q = TypedTerm("Q", FunType(type_e, type_t))
    x = TypedTerm("x", type_e)
    y = TypedTerm("y", type_e)
    t = TypedExpr.factory(P, x)
    t2 = TypedExpr.factory(Q, x)
    body = TypedExpr.factory("&", t, t) | t
    p = TypedTerm("p", type_t)
    testf = LFun(None, body, vartype=type_e)

    pmw_test1 = LFun('p', LFun('x', t & p, vartype=type_e), vartype=type_t)
    pmw_test1b = LFun('x', t & t2, vartype=type_e)
    # test: when a free variable in a function scopes under an operator, do not
    # bind the variable on application
    assert pmw_test1.apply(t2) != pmw_test1b

    # Different version of the same test: direct variable substitution
    test2 = TypedExpr.factory("L y_e : L x_e : y_e")
    test2b = TypedExpr.factory("L x_e : x_e")
    assert test2.apply(x) != test2b

test_setup()
