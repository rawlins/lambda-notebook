from lamb import meta, types, lang
from lamb.meta import te, tp

# combinators for predicate modification
pm_combinator = te("L f_<e,t> : L g_<e,t> : L x_e : f(x) & g(x)")
pm_generalized_combinator = te("L f_<X,t> : L g_<X,t> : L x_X : f(x) & g(x)")



# the Geach combinator -- for the g rule, and for function composition
geach_combinator = te("L g_<Y,Z> : L f_<X,Y> : L x_X : g(f(x))")

# for the sake of posterity, here is a way of constructing the Geach combinator
# without polymorphism:

def build_geach_combinator(gtype, ftype):
    body = meta.term("g", gtype)(meta.term("f", ftype)(meta.term("x", ftype.left)))
    combinator = meta.LFun(gtype,
                           meta.LFun(ftype,
                                     meta.LFun(ftype.left, body, varname="x"),
                                     varname="f"),
                           varname="g")
    return combinator

def function_composition_nopoly(g, f):
    if (not (g.type.functional() and f.type.functional()
             and g.type.left == f.type.right)):
        raise types.TypeMismatch(g, f, "Function composition")
    combinator = geach_combinator(g.type, f.type)
    result = (combinator(g)(f)).reduce_all()
    return result

def geach_shift(fun, f_type_left):
    combinator = geach_combinator(fun.type, types.FunType(f_type_left,
                                                          fun.type.left))
    return combinator(fun).reduce_all()

def g_e_shift(fun, assignment=None):
    if not fun.type.functional():
        raise types.TypeMismatch(fun, None, "g-shift for type e")
    result = geach_shift(fun.content.under_assignment(assignment), types.type_e)
    return lang.UnaryComposite(fun, result)

def g_et_shift(fun, assignment=None):
    if not fun.type.functional():
        raise types.TypeMismatch(fun, None, "g-shift for type <e,t>")
    result = geach_shift(fun.content.under_assignment(assignment),
                         types.type_property)
    return lang.UnaryComposite(fun, result)



# Type lifting

lift_combinator_t = te("L f_X : L g_<X,t> : g(f)")
lift_combinator = te("L f_X : L g_<X,Y> : g(f)")


# for the sake of posterity:

def lift(arg, ltype):
    larg_type = types.FunType(arg.type, ltype)
    combinator = meta.LFun(arg.type, meta.LFun(larg_type,
        meta.term("g", larg_type)(meta.term("f", arg.type)), "g"), "f")
    result = combinator(arg).reduce_all()
    return result

def lift_t_shift(arg, assignment=None):
    result = lift(arg.content.under_assignment(assignment), types.type_t)
    return lang.UnaryComposite(arg, result)


# Z rule

z_combinator_e = te("(λ f_<X,<e,Z>>: (λ g_<e,X>: (λ x_e: f(g(x))(x))))")
z_combinator = te("(λ f_<X,<Y,Z>>: (λ g_<Y,X>: (λ x_Y: f(g(x))(x))))")


# for the sake of posterity:

def z_combinator_fun(ftype):
    # does not check types...
    left_type = ftype.left
    g_type = types.FunType(types.type_e, left_type)
    body = meta.term("f", ftype)(meta.term("g", g_type)(
        meta.term("x", types.type_e)))(meta.term("x", types.type_e))
    comb = meta.LFun(ftype, meta.LFun(g_type, meta.LFun(types.type_e,
        body, varname="x"),varname="g"),varname="f")
    return comb

def z_shift(fun, assignment=None):
    if not (fun.type.functional() and fun.type.right.functional()
            and fun.type.right.left == types.type_e):
        raise types.TypeMismatch(fun, None, "z-shift")
    result = z_combinator(fun.type)(
        fun.content.under_assignment(assignment)).reduce_all()
    return lang.UnaryComposite(fun, result)

def continuize_combinator_fun(typ):
    cont_type = types.FunType(typ, types.type_t)
    comb = lang.te("L x_%s : L f_%s : f(x)" % (repr(typ), repr(cont_type)))
    return comb

def continuize_app_combinator(ftype, argtype):
    try:
        b = ftype.left.left
    except:
        # note that exceptions other than TypeMismatch will halt
        # composition; a TypeMismatch just signals that a particular attempt
        # won't succeed.
        raise types.TypeMismatch(ftype, None, "Not a continuized function type")
    try:
        abar = types.FunType(b.right, types.type_t)
    except:
        raise types.TypeMismatch(ftype, None, "Not a continuized function type")
    try:
        c = argtype.left.left
    except:
        raise types.TypeMismatch(argtype, None, "Not a continuation type")
    comb_s = ("L f_%s : L arg_%s : L abar_%s : f(L b_%s : arg(L c_%s : abar(b(c))))"
                % (repr(ftype), repr(argtype), repr(abar), repr(b), repr(c)))
    comb = te(comb_s) # parse the combinator string
    return comb

def continuized_apply(a1, a2, assignment=None):
    comb = continuize_app_combinator(a1.type, a2.type)
    result = comb(a1.content.under_assignment(assignment))(
                                    a2.content.under_assignment(assignment))
    return lang.BinaryComposite(a1, a2, result)

ca_op = lang.BinaryCompositionOp("CA", continuized_apply, reduce=True)

# assumes already continuized types
def continuize_app_combinator2(ftype, argtype):
    try:
        b = ftype.left.left
    except:
        raise types.TypeMismatch(ftype, None, "Not a continuation type")
    try:
        abar = types.FunType(b.right, types.type_t)
    except:
        raise types.TypeMismatch(ftype, None, "Not a continuized function type")
    try:
        c = argtype.left.left
    except:
        raise types.TypeMismatch(argtype, None, "Not a continuation type")
    comb_s = ("L f_%s : L arg_%s : L abar_%s : arg(L c_%s : f(L b_%s : abar(b(c))))" %
                    (repr(ftype), repr(argtype), repr(abar), repr(c), repr(b)))
    comb = te(comb_s)
    return comb


def continuized_apply2(a1, a2, assignment=None):
    comb = continuize_app_combinator2(a1.type, a2.type)
    result = comb(a1.content.under_assignment(assignment))(
                                    a2.content.under_assignment(assignment))
    return lang.BinaryComposite(a1, a2, result)

ca2_op = lang.BinaryCompositionOp("CA2", continuized_apply2, reduce=True)

