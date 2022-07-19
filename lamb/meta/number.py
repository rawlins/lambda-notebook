import lamb.meta.core, lamb.types
from lamb.meta.core import op, registry
from lamb.types import type_t, type_n


def setup_operators():
    global registry
    def add_n_op(c):
        registry.add_operator(c, *[type_n for x in range(c.arity)])

    # TODO: unary +, for better error msgs if nothing else
    add_n_op(UnaryNegativeExpr)
    add_n_op(UnaryPositiveExpr)
    add_n_op(BinaryLExpr)
    add_n_op(BinaryGExpr)
    add_n_op(BinaryLeqExpr)
    add_n_op(BinaryGeqExpr)
    add_n_op(BinaryPlusExpr)
    add_n_op(BinaryMinusExpr)
    add_n_op(BinaryDivExpr)
    add_n_op(BinaryTimesExpr)
    add_n_op(BinaryExpExpr)

@op("-", type_n, type_n)
def UnaryNegativeExpr(self, x):
    return -x

@op("+", type_n, type_n)
def UnaryPositiveExpr(self, x):
    return +x

@op("<", type_n, type_t)
def BinaryLExpr(self, x, y):
    return x < y

@op("<=", type_n, type_t, op_latex="\\leq{}")
def BinaryLeqExpr(self, x, y):
    return x <= y

@op(">", type_n, type_t)
def BinaryGExpr(self, x, y):
    return x > y

@op(">=", type_n, type_t, op_latex="\\geq{}")
def BinaryGeqExpr(self, x, y):
    return x >= y

@op("+", type_n, type_n)
def BinaryPlusExpr(self, x, y):
    return x + y

@op("-", type_n, type_n)
def BinaryMinusExpr(self, x, y):
    return x - y

@op("*", type_n, type_n)
def BinaryTimesExpr(self, x, y):
    return x * y

@op("/", type_n, type_n)
def BinaryDivExpr(self, x, y):
    return x / y

@op("**", type_n, type_n)
def BinaryExpExpr(self, x, y):
    return x ** y
