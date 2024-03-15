from lamb import meta, types, lang
from lamb.meta import te, tp


# combinators for predicate modification
pm_combinator = te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")
pm_generalized_combinator = te("L f_<X,t> : L g_<X,t> : L x_X : f(x) & g(x)")


# the Geach combinator -- for the g rule, and for function composition
geach_combinator = te("L g_<Y,Z> : L f_<X,Y> : L x_X : g(f(x))")


def fun_compose(g, f):
    if not (g.type.functional() and f.type.functional()):
        # the combinator would error for this, but the error is a bit more
        # inscrutable:
        raise types.TypeMismatch(g, f, "Function composition requires functions")
    return (geach_combinator(g)(f)).reduce_all()


def geach_shift(fun):
    return lang.UnaryComposite(fun, geach_combinator(fun).reduce_all())


# for the sake of posterity, here is a way of constructing the Geach combinator
# without polymorphism:
def build_geach_combinator(gtype, ftype):
    body = meta.term("g", gtype)(meta.term("f", ftype)(meta.term("x", ftype.left)))
    combinator = meta.LFun('g',
                           meta.LFun('f',
                                     meta.LFun('x', body, vartype=ftype.left),
                                     vartype=ftype),
                           vartype=gtype)
    return combinator


# Type lifting
# here's an example specialization:
lift_combinator_t = te("L f_X : L g_<X,t> : g(f)")
# and the general version:
lift_combinator = te("L f_X : L g_<X,Y> : g(f)")


# for the sake of posterity, a non-polymorphic implementation of lift:
def build_lift(arg, ltype):
    larg_type = types.FunType(arg.type, ltype)
    combinator = meta.LFun('f',
                           meta.LFun('g',
                                     larg_type, meta.term('g', larg_type)(meta.term('f', arg.type)),
                                     vartype=larg_type),
                           vartype=arg.type)
    return combinator(arg).reduce_all()


# Z rule


# it is easier to get a sense for this by looking at a specialized version:
z_combinator_e = te("(λ f_<X,<e,Z>>: (λ g_<e,X>: (λ x_e: f(g(x))(x))))")


# but really, here's what we want:
z_combinator = te("(λ f_<X,<Y,Z>>: (λ g_<Y,X>: (λ x_Y: f(g(x))(x))))")


def z_shift(fun, assignment=None):
    result = z_combinator(fun).reduce_all()
    return lang.UnaryComposite(fun, result)


# for the sake of posterity, here's a non-polymorphic builder for z_combinator_e:
def build_z_combinator_fun(ftype):
    # does not itself check types...
    left_type = ftype.left
    g_type = types.FunType(types.type_e, left_type)
    body = meta.term("f", ftype)(meta.term("g", g_type)(
        meta.term("x", types.type_e)))(meta.term("x", types.type_e))
    comb = meta.LFun('f',
                     meta.LFun('g',
                               meta.LFun('x', body, vartype=types.type_e),
                               vartype=g_type),
                     vartype=ftype)
    return comb

