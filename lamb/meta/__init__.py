__all__ = ['parser', 'core', 'boolean', 'meta', 'number', 'ply', 'quantifiers', 'sets', 'typeref', 'test']

# -*- coding: utf-8 -*-
from numbers import Number
from lamb import types, utils, parsing, display
from lamb.types import TypeMismatch, type_e, type_t, type_n
from lamb.types import type_property, type_transitive, BasicType, FunType

from lamb.meta import parser
from lamb.meta import core, boolean, meta, number, ply, quantifiers, sets
from lamb.meta import typeref
from lamb.meta.core import TypedExpr, TypedTerm, ApplicationExpr
from lamb.meta.core import LFun, BindingOp
from lamb.meta.core import Tuple, TupleIndex, Partial, Disjunctive, BinaryGenericEqExpr
from lamb.meta.core import base_language, logger, op
from lamb.meta.core import get_type_system, set_type_system, ts_unify, ts_compatible
from lamb.meta.core import te, is_te, tp, term, let_wrapper
from lamb.meta.core import unify, global_namespace
from lamb.meta.core import get_language

from lamb.meta.ply import simplify_all, derived, default_sopts, collect, join

from lamb.meta.boolean import true_term, false_term

from lamb.meta.meta import truthtable, truthtable_equiv, MetaTerm, Assignment, Model
from lamb.meta.meta import compiled, exec


###############
#
# Setup
#
###############

def setup_operators(language):
    # generic equivalence needs to be first, as it has an extremely general
    # viability check that several specialized equivalence operators will
    # override. The class appears early enough that the type signature needs
    # to be specified here.
    language.registry.add_operator(core.BinaryGenericEqExpr, tp("X"), tp("X"))
    language.registry.add_binding_op(LFun)
    language.registry.add_operator(core.ChainFun, tp("<X,Y>"), tp("<X,Y>"))
    language.registry.add_operator(core.Partial, tp("X"), tp("t"))
    language.registry.add_operator(core.Body, tp("X"))
    language.registry.add_operator(core.Condition, tp("X"))
    # TODO: convert these to real operators
    language.add_local("Fun", core.MapFun)
    language.add_local("Disjunctive", core.Disjunctive)
    for m in [typeref, boolean, number, sets, quantifiers]:
        m.setup_operators(language)

def default_metalanguage(force=True):
    base_language.registry.clear()
    try:
        setup_operators(base_language)
    except Exception as e:
        if force:
            raise e
        print("Failed to load metalanguage! Starting without one...")
        core.reset() # if the type system is broken, this could still fail


def reset():
    core.reset()
    default_metalanguage()


default_metalanguage()

# this needs to happen after the metalanguage is set up
from lamb.meta import test

