import lamb.meta.core, lamb.types
from lamb.meta.core import op, registry, TypedExpr
from lamb.types import type_t, type_n, is_numeric


def setup_operators():
    global registry
    def add_n_op(c):
        registry.add_operator(c, *[type_n for x in range(c.arity)])

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
    # in order to ensure that constant numerics actually have a sign, we apply
    # simplify to any expressions involving both numeric types. Without this,
    # te("-1") etc would parse as UnaryNegativeExpr(MetaTerm(1)), which confuses
    # things like tuple indexing. With this, it'll parse just as MetaTerm(-1).
    def unary_presimplify(e):
        # just calling `simplify` here is enough to trigger the recursion we
        # need
        return e.simplify()
    registry.set_custom_transform(UnaryPositiveExpr, unary_presimplify)
    registry.set_custom_transform(UnaryNegativeExpr, unary_presimplify)


@op("-", type_n, type_n, python_only=False)
def UnaryNegativeExpr(self, x):
    if isinstance(x, TypedExpr):
        if isinstance(x, UnaryNegativeExpr):
            return x[0].copy() # will trigger the custom transform code
        else:
            return self
    return -x

@op("+", type_n, type_n, python_only=False)
def UnaryPositiveExpr(self, x):
    # this is essentially a noop
    return x

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

BinaryPlusExpr.commutative = True
BinaryPlusExpr.associative = True

@op("-", type_n, type_n)
def BinaryMinusExpr(self, x, y):
    return x - y

@op("*", type_n, type_n)
def BinaryTimesExpr(self, x, y):
    return x * y

BinaryTimesExpr.commutative = True
BinaryTimesExpr.associative = True

@op("/", type_n, type_n)
def BinaryDivExpr(self, x, y):
    return x / y

# XX use superscript
@op("**", type_n, type_n, op_latex="{**}")
def BinaryExpExpr(self, x, y):
    return x ** y
