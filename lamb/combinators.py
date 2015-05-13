from lamb import meta, types
from lamb.meta import te, tp

# combinators for predicate modification
pm_combinator = meta.pm_op  # te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")
pm_generalized_combinator = te("L f_<X,t> : L g_<X,t> : L x_X : f(x) & g(x)")



# the Geach combinator -- for the g rule, and for function composition
geach_combinator = te("L g_<Y,Z> : L f_<X,Y> : L x_X : g(f(x))")

# for the sake of posterity, here is a way of constructing the Geach combinator without polymorphism:

def build_geach_combinator(gtype, ftype):
    body = meta.term("g", gtype)(meta.term("f", ftype)(meta.term("x", ftype.left)))
    combinator = meta.LFun(gtype, meta.LFun(ftype, meta.LFun(ftype.left, body,varname="x"),varname="f"), varname="g")
    return combinator

def function_composition_nopoly(g, f):
    if (not (g.type.functional() and f.type.functional()
             and g.type.left == f.type.right)):
        raise types.TypeMismatch(g, f, "Function composition")
    combinator = geach_combinator(g.type, f.type)
    result = (combinator(g)(f)).reduce_all()
    return result


