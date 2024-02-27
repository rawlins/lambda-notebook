import logging, unittest, random, enum
import collections.abc
import lamb
from lamb import types, parsing
from lamb.types import TypeMismatch, type_e, type_t, type_n
from . import core, boolean, number, sets, meta
from .core import logger, te, tp, get_type_system, TypedExpr, LFun, TypedTerm
from .meta import MetaTerm
from .ply import alphanorm


def repr_parse(e):
    result = te(repr(e), let=False)
    return result == e


def random_term(typ=None, blockset=None, usedset=set(), prob_used=0.8,
                                            prob_var=0.5, max_type_depth=1):
    return TypedTerm.random(random_ctrl_fun=None,
                            typ=typ,
                            blockset=blockset,
                            usedset=usedset,
                            prob_used=prob_used,
                            prob_var=prob_var,
                            max_type_depth=max_type_depth)

def random_binding_expr(ctrl, max_type_depth=1):
    global random_used_vars
    ts = get_type_system()
    options = [boolean.ForallUnary, boolean.ExistsUnary, boolean.ExistsExact]
    op_class = random.choice(options)
    var_type = ts.random_type(max_type_depth, 0.5)
    variable = random_term(var_type, usedset=random_used_vars, prob_used=0.2,
                                                                prob_var=1.0)
    random_used_vars |= {variable}
    return op_class(variable, ctrl(typ=type_t))

def random_lfun(typ, ctrl):
    global random_used_vars
    ftyp = typ
    if ftyp is not None and not isinstance(ftyp, types.FunType):
        ftyp = get_type_system().unify(typ, tp("<?,?>"))
    # n.b.: unification here can get ? types, if `typ` is a variable. So use
    # with care -- e.g. it can lead to repr_parse failures.
    if ftyp is None:
        raise ValueError(f"Need a functional type to generate random LFuns, got {typ}")
    input_type = ftyp.left
    body_type = ftyp.right
    variable = random_term(input_type, usedset=random_used_vars, prob_used=0.2,
                                                        prob_var=1.0)
    random_used_vars |= {variable}
    return LFun(variable, ctrl(typ=body_type))

def random_lfun_force_bound(typ, ctrl):
    global random_used_vars
    ftyp = typ
    if ftyp is not None and not isinstance(ftyp, types.FunType):
        ftyp = get_type_system().unify(typ, tp("<?,?>"))
    if ftyp is None:
        raise ValueError(f"Need a functional type to generate random LFuns, got {typ}")
    input_type = ftyp.left
    body_type = ftyp.right
    variable = random_term(input_type, usedset=random_used_vars, prob_used=0.2,
                                                        prob_var=1.0)
    random_used_vars |= {variable}
    return LFun(variable, random_pred_combo_from_term(body_type, ctrl,
                                                    termset=random_used_vars))


random_types = [type_t]
random_ops = ["&", "|", ">>", "%"]

def random_tf_op_expr(ctrl_fun):
    op = random.choice(random_ops)
    while op not in core.registry.ops:
        op = random.choice(random_ops)
    op = random.choice(core.registry.get_descs(op, type_t, type_t)) # probably size 1
    if op.has_blank_types():
        raise NotImplementedError
    return op.cls(*[ctrl_fun(typ=t) for t in op.targs])


# use this to try to get more reused bound variables (which tend to have odd
# types when generated randomly)
def random_pred_combo_from_term(output_type, ctrl, termset):
    if len(termset) == 0:
        raise ValueError("Can't generate an expression from a term without any terms!")
    if output_type is None:
        output_type = type_t
    ts = get_type_system()
    term = (random.choice(list(termset))).copy()
    pred_type = ts.unify_ar(term.type, output_type)
    if pred_type is None:
        raise ValueError(f"Incompatible predicate {term} for requested type {output_type}")
    pred = ctrl(typ=pred_type)
    return pred(term)

def random_fa_combo(output_type, ctrl, max_type_depth=1):
    if output_type is None:
        output_type = type_t
    ts = get_type_system()
    input_type = ts.random_type(max_type_depth, 0.5, allow_variables=False)
    fun_type = types.FunType(input_type, output_type)
    result = (ctrl(typ=fun_type))(ctrl(typ=input_type))
    return result

def random_from_class(cls, max_depth=1, used_vars=None):
    global random_used_vars
    if used_vars is None:
        used_vars = set()
    random_used_vars = used_vars

    def ctrl(**args):
        global random_used_vars
        return random_expr(depth=max_depth-1, used_vars=random_used_vars,
                                                                    **args)

    return cls.random(ctrl)


random_set_ops = [sets.SetUnion, sets.SetIntersection, sets.SetDifference]
random_set_rels = [sets.SetEquivalence, sets.SetSubset, sets.SetProperSubset,
                   sets.SetSupset, sets.SetProperSupset, sets.SetContains]


def random_set_expr(ctrl, typ=None):
    if typ is not None and not isinstance(typ, types.SetType):
        raise ValueError(f"Generating a random set operator expression requires a set type, got {typ}")
    return random.choice(random_set_ops).random(ctrl, typ=typ)


def random_set_rel(ctrl, typ=None):
    if typ is not None and not isinstance(typ, types.SetType):
        raise ValueError(f"Generating a random set relation expression requires a set type, got {typ}")
    return random.choice(random_set_rels).random(ctrl, typ=typ)


# ugh, need to find a way to do this not by side effect
global random_used_vars
random_used_vars = set()

class RType(enum.Enum):
    FA_COMBO = 1
    BOOLEAN_OP_EXPR = 2
    BINDING_EXPR = 3
    LFUN = 4
    LFUN_BOUND = 5 # ensures that there is a bound variable
    TERM_PRED_COMBO = 6
    SET_RELATION = 7
    SET_OP = 8

def random_expr(typ=None, depth=1, max_type_depth=1, options=None, used_vars=None):
    """Generate a random expression of the specified type `typ`, with an AST of
    specified `depth`, according to schemas optionally supplied by `options`
    (which should use values from the enum `test.RType`).

    This won't generate absolutely everything, and I haven't tried to make this
    use some sensible distribution over expressions (whatever that would be).

    If `options` is None, use all schemas compatible with the provided type.
    If both `typ` and `options` are `None`, uses all schemas compatible with
    type `t`. Several options (LFUN and LFUN_BOUND) require, if specified
    explicitly, a matching (functional) type and will error if this isn't
    provided. Other options that allow type arguments do not require them, and
    will default to `t` if none are provided.

    The schema `TERM_PRED_COMBO` requires `used_vars` to provide a non-empty
    TypedExpr variables, that it will attempt to use, and will error if this
    isn't provided. (This is primarily intended to be used recursively.)
    """
    # An alternative approach would be to generate a random AST first, and fill
    # it in.

    global random_used_vars
    initial_call = False
    if used_vars is None:
        initial_call = True
        used_vars = set()
    random_used_vars = used_vars
    if typ is None and options is None:
        typ = random.choice(random_types)
    if typ == types.SetType:
        typ = types.SetType(get_type_system().random_type(max_type_depth, 0.5))
    if depth == 0:
        term = random_term(typ, usedset=random_used_vars, max_type_depth=max_type_depth)
        random_used_vars |= {term}
        return term
    else:
        # possibilities:
        #  1. any typ: function-argument combination resulting in typ
        #  2. if typ is type_t: operator expression of typ (exclude non type_t
        #     options for now)
        #  3. if typ is type_t: binding expression of type_t
        #  4. if typ is functional: LFun of typ
        #  5. if typ is a SetType: a set operation of that type
        # ignore sets for now (variables with set types can be generated as
        # part of option 1)
        # ignore iota for now
        if options and not isinstance(options, collections.abc.Sequence):
            options = [options]
        if not options:
            options = [RType.FA_COMBO]
            if typ == type_t:
                options.append(RType.BOOLEAN_OP_EXPR)
                options.append(RType.BINDING_EXPR)
                options.append(RType.SET_RELATION)
            if typ.functional() and not isinstance(typ, types.VariableType):
                # If `typ` is a variable type, these options can lead to ?
                # types in formulas. This is useful in general, but exclude
                # by default, so that it doesn't cause `repr_parse` failures.
                options.append(RType.LFUN)
                options.append(RType.LFUN_BOUND)
            if isinstance(typ, types.SetType):
                options.append(RType.SET_OP)
            if depth == 1 and len(random_used_vars) > 0:
                options.extend([RType.TERM_PRED_COMBO] * 4) # try to reuse vars a bit more

        choice = random.choice(options)
        def ctrl(**args):
            global random_used_vars
            return random_expr(depth=depth-1, used_vars=random_used_vars,
                                                                        **args)
        if choice == RType.FA_COMBO:
            return random_fa_combo(typ, ctrl, max_type_depth=max_type_depth)
        elif choice == RType.BOOLEAN_OP_EXPR:
            if typ is not None and typ != type_t:
                logger.warning(f"Ignoring requested non-t type {typ} for a boolean operator expression")
            return random_tf_op_expr(ctrl)
        elif choice == RType.BINDING_EXPR:
            if typ is not None and typ != type_t:
                logger.warning(f"Ignoring requested non-t type {typ} for a binding operator expression")
            return random_binding_expr(ctrl, max_type_depth=max_type_depth)
        elif choice == RType.LFUN:
            return random_lfun(typ, ctrl)
        elif choice == RType.LFUN_BOUND:
            return random_lfun_force_bound(typ, ctrl)
        elif choice == RType.TERM_PRED_COMBO:
            return random_pred_combo_from_term(typ, ctrl, random_used_vars)
        elif choice == RType.SET_RELATION:
            # defer type choice to the class
            if typ is not None and typ != type_t:
                logger.warning(f"Ignoring requested non-t type {typ} for a set relation expression")
            return random_set_rel(ctrl)
        elif choice == RType.SET_OP:
            return random_set_expr(ctrl, typ=typ)
        else:
            raise NotImplementedError


def random_pure_boolean(depth=1, used_vars=None, **args):
    global random_used_vars
    if used_vars is None:
        used_vars = set()
    random_used_vars = used_vars
    if depth == 0:
        term = random_term(type_t, usedset=random_used_vars)
        random_used_vars |= {term}
        return term
    else:
        def ctrl(**args):
            global random_used_vars
            return random_pure_boolean(depth=depth-1, used_vars=random_used_vars,
                                                                        **args)
        return random_tf_op_expr(ctrl)

def test_repr_parse_abstract(self, depth):
    for i in range(1000):
        x = random_expr(depth=depth)
        result = repr_parse(x)
        latex_str = x.latex_str() # also test that this doesn't crash -- can't
                                  # easily test actual contents.
        if not result:
            print("Failure on depth %i expression '%s'" % (depth, repr(x)))
        self.assertTrue(result)

def testsimp(self, a, b, all=False):
    if all:
        intermediate = a.simplify_all()
    else:
        intermediate = a.simplify()
    teb = te(b)
    if intermediate != teb:
        print("Failed simplification test: '%s == %s'" % (repr(a), repr(b)))
    self.assertEqual(intermediate, teb)
    return intermediate


te_classes = [core.ApplicationExpr,
              core.LFun,
              core.Tuple,
              core.TupleIndex,
              core.TypedTerm,
              core.Partial,
              core.Disjunctive,
              meta.MetaTerm,
              boolean.UnaryNegExpr,
              boolean.BinaryAndExpr,
              boolean.BinaryOrExpr,
              boolean.BinaryArrowExpr,
              boolean.BinaryBiarrowExpr,
              boolean.BinaryNeqExpr,
              boolean.ForallUnary,
              boolean.ExistsUnary,
              boolean.ExistsExact,
              boolean.IotaUnary,
              boolean.IotaPartial,
              number.UnaryNegativeExpr,
              number.UnaryPositiveExpr,
              number.BinaryLExpr,
              number.BinaryLeqExpr,
              number.BinaryGExpr,
              number.BinaryGeqExpr,
              number.BinaryPlusExpr,
              number.BinaryMinusExpr,
              number.BinaryDivExpr,
              number.BinaryExpExpr,
              sets.SetContains,
              sets.ConditionSet,
              sets.ListedSet]

class MetaTest(unittest.TestCase):
    def setUp(self):
        self.ident = te("L x_e : x") 
        self.ia = TypedExpr.factory(self.ident, "y")
        self.ib = LFun(type_e, self.ia, "y")
        self.P = TypedTerm("P", types.FunType(type_e, type_t))
        self.Q = TypedTerm("Q", types.FunType(type_e, type_t))
        self.x = TypedTerm("x", type_e)
        self.y = TypedTerm("y", type_e)
        self.t = TypedExpr.factory(self.P, self.x)
        self.t2 = TypedExpr.factory(self.Q, self.x)
        self.body = TypedExpr.factory("&", self.t, self.t) | self.t
        self.p = TypedTerm("p", type_t)
        self.testf = LFun(type_e, self.body)

    def test_basic(self):
        # equality basics
        self.assertEqual(self.P, self.P)
        self.assertEqual(self.x, self.x)
        self.assertEqual(self.testf, self.testf)
        self.assertNotEqual(self.P, self.Q)
        self.assertNotEqual(self.x, self.y)


    def test_class_random(self):
        for c in te_classes:
            for i in range(100):
                x = random_from_class(c)
                # verify some things about terms
                # XX partial metaterms? I think they may be possible...
                self.assertTrue(x.meta() == (isinstance(x, MetaTerm)))
                if c != core.Tuple and c != sets.ListedSet:
                    # XX 0 length tuple/set doesn't count as a term, but perhaps
                    # they should? even as a metaterm of some kind?
                    if c == core.Partial:
                        l = len(x.body)
                    else:
                        l = len(x)
                    self.assertTrue(x.term() == (not l), f"{x}")

    def test_copy(self):
        for c in te_classes:
            if c == number.UnaryNegativeExpr or c == number.UnaryPositiveExpr:
                # the pre-simplify step for these two classes breaks identity
                # on copy, if the contained object is manually constructed from
                # a negative number. This can only really happen through this
                # test, so skip it.
                continue

            for i in range(50):
                x = random_from_class(c)
                self.assertEqual(x, x.copy())
                self.assertEqual(x, x.copy_local(*x))


    def test_parse(self):
        # overall: compare parsed `TypedExpr`s with constructed `TypedExpr`s
        # basic operator syntax
        self.assertEqual(TypedExpr.factory(
            "(P_<e,t>(x_e) & P_<e,t>(x_e)) | P_<e,t>(x_e)"), self.body)
        # parenthesis reduction
        self.assertEqual(TypedExpr.factory(
            "((P_<e,t>(x_e) & P_<e,t>(x_e)) | (P_<e,t>(x_e)))"), self.body)
        # parenthesis grouping
        self.assertNotEqual(TypedExpr.factory(
            "P_<e,t>(x_e) & (P_<e,t>(x_e) | P_<e,t>(x_e))"), self.body)
        # variable binding syntax
        self.assertEqual(TypedExpr.factory("L x_e : x_e"), self.ident)
        self.assertRaises(parsing.ParseError, TypedExpr.factory, "L x_e : x_t")
        logger.setLevel(logging.WARNING)
        te("L x: L y: In(y)(x)")
        logger.setLevel(logging.INFO)

    def test_terms(self):
        self.assertTrue(te("x_e").term())
        self.assertTrue(te("X_e").term())
        self.assertTrue(te("_c1_e").term())
        self.assertTrue(te("True").term())
        self.assertTrue(te("10").term())
        # term() is verified in random objects

        # basic comparison. These look simple here, but are a bit tricky
        # because python 0/1 compare as equal to python False/True; the latter
        # are really a subtype of int and therefore numeric.
        self.assertEqual(MetaTerm(True), boolean.true_term)
        self.assertEqual(MetaTerm(False), boolean.false_term)
        self.assertEqual(MetaTerm(False), False)
        self.assertEqual(MetaTerm(True), True)
        self.assertEqual(bool(MetaTerm(True)), True)
        self.assertNotEqual(MetaTerm(False), None)
        self.assertNotEqual(MetaTerm(False), 0)
        self.assertNotEqual(MetaTerm(True), 1)
        self.assertNotEqual(MetaTerm(False), MetaTerm(0))
        self.assertNotEqual(MetaTerm(True), MetaTerm(1))
        # default types for numeric/bool references
        for i in [0,1]:
            self.assertEqual(te(f"{i}_n"), te(f"{i}"))
            self.assertNotEqual(te(f"{i}_t"), te(f"{i}"))
        for i in [False,True]:
            self.assertNotEqual(te(f"{i}_n"), te(f"{i}"))
            self.assertEqual(te(f"{i}_t"), te(f"{i}"))
        # type coercion in parsing for numeric/bool references:
        self.assertEqual(te("0_t"), te("False"))
        self.assertEqual(te("1_t"), te("True"))
        self.assertEqual(te("2_t"), te("True"))
        self.assertEqual(te("False_n"), te("0"))
        self.assertEqual(te("True_n"), te("1"))
        # once constructed, completely distinct types (some overlap with above
        # tests, but here we also check parsing):
        self.assertNotEqual(te("False_n"), te("0_t"))
        self.assertNotEqual(te("True_n"), te("1_t"))
        self.assertNotEqual(te("False_t"), te("0_n"))
        self.assertNotEqual(te("True_t"), te("1_n"))
        # no coercion for other types:
        self.assertRaises(TypeMismatch, te, "True_e")
        self.assertRaises(TypeMismatch, te, "1_e")
        self.assertRaises(TypeMismatch, te, "_c1_t")
        self.assertRaises(TypeMismatch, te, "_c1_n")
        # no coercion on direct constructor calls:
        for i in [0,1]:
            self.assertRaises(TypeMismatch, MetaTerm, i, typ=type_t)
        for i in [False,True]:
            self.assertRaises(TypeMismatch, MetaTerm, i, typ=type_n)

        self.assertEqual(MetaTerm(3), 3)
        self.assertEqual(te("-3"), -3)   # unary - is pre-simplified
        self.assertEqual(te("---3"), -3) # unary - is pre-simplified
        self.assertEqual(te("+3"), 3)    # unary + is pre-simplified
        self.assertEqual(MetaTerm("c1"), "_c1")
        self.assertEqual(MetaTerm("c1"), MetaTerm("_c1"))
        self.assertNotEqual(MetaTerm(False), MetaTerm(True))

        self.assertRaises(types.TypeParseError, te, "_c1__")     # wrong for various reasons, but the error is a type error
        self.assertRaises(parsing.ParseError, te, "__c1")        # extra _ at beginning
        self.assertRaises(parsing.ParseError, TypedTerm, True)   # no domain element references in TypedTerms
        self.assertRaises(parsing.ParseError, TypedTerm, 3)      # no domain element references in TypedTerms
        self.assertRaises(parsing.ParseError, TypedTerm, "_c1")  # no _ TypedTerms
        self.assertRaises(parsing.ParseError, MetaTerm, "_c1_e") # invalid string format
        self.assertRaises(parsing.ParseError, MetaTerm, "_x1")   # x is an invalid prefix by default

        self.assertNotEqual(MetaTerm("c1", typ=type_e), te("c1_e"))
        self.assertNotEqual(MetaTerm("c1", typ=type_e), TypedTerm("c1", typ=type_e))
        # the following TypedTerm can't be constructed via the parser
        self.assertNotEqual(MetaTerm(True, typ=type_t), TypedTerm("True", typ=type_t))

        # simplify produces a MetaTerm. some overlap with simplification code here
        self.assertEqual(te("True & True").simplify(), MetaTerm(True))

    def test_complex_terms(self):
        t1 = tp("<e,t>")
        content1 = {'_c1': te("True_t"), '_c2': True, '_c3': False}
        self.assertEqual(MetaTerm(content1), MetaTerm(content1, typ=t1))
        content2 = {'_c1', '_c2'}
        self.assertEqual(MetaTerm(content2, setfun=True), MetaTerm(content2, typ=t1))
        for e in ['_c1', '_c2', '_c3']:
            self.assertEqual(MetaTerm(content1, typ=t1)(MetaTerm(e)).reduce(), e in content2)
            self.assertEqual(MetaTerm(content2, typ=t1)(MetaTerm(e)).reduce(), e in content2)
        # currently: raises OutOfDomain only on reduce call
        self.assertRaises(meta.OutOfDomain, MetaTerm(content1, typ=t1)(MetaTerm('_c4')).reduce)
        self.assertEqual(MetaTerm(content2, typ=t1)(MetaTerm('_c4')).reduce(), False)

        t2 = tp("<(e,e),t>")
        content3 = {('_c1', '_c1'): te("True_t"), ('_c1', '_c2'): True}
        self.assertEqual(MetaTerm(content3), MetaTerm(content3, typ=t2))
        content4 = {('_c1', '_c1'), ('_c1', '_c2')}
        self.assertEqual(MetaTerm(content4, setfun=True), MetaTerm(content4, typ=t2))

        self.assertRaises(TypeMismatch, MetaTerm, {False, '_c1'})
        self.assertRaises(parsing.ParseError, MetaTerm, {'_x1', '_c1'})

    def test_reduce(self):
        self.assertEqual(self.ident(self.y).reduce(), self.y)

        # test: when a free variable in a function scopes under an operator, do
        # not bind the variable on application        
        pmw_test1 = LFun(type_t, LFun(type_e, self.t & self.p, "x"), "p")
        pmw_test1b = LFun(type_e, self.t & self.t2, "x")
        self.assertNotEqual(pmw_test1.apply(self.t2), pmw_test1b)

        # Different version of the same test: direct variable substitution
        test2 = TypedExpr.factory("L y_e : L x_e : y_e")
        test2b = TypedExpr.factory("L x_e : x_e")
        self.assertNotEqual(test2.apply(self.x), test2b)

        # test for accidental collisions from alpha conversions, added Apr 2015
        test3 = TypedExpr.factory(
            "(L xbar_<e,t> : L x_e : xbar(x))(L z_e : P_<(e,e,e),t>(x_e,z_e, x1_e))")
        test3 = test3.reduce_all()
        self.assertNotEqual(test3[1][1][0], test3[1][1][1])
        self.assertNotEqual(test3[1][1][0], test3[1][1][2])
        self.assertNotEqual(test3[1][1][1], test3[1][1][2])

        # test some relatively nasty reduction cases
        self.assertEqual(te("(L x_e : (L f_<e,e> : f(f(f(f(f(x))))))(L x_e : x))").reduce_all(),
            test2b)
        self.assertEqual(te("(L f_<e,e> : L g_<e,e> : L x_e : g(f(x)))(L x_e : x)(L y_e : y)").reduce_all(),
            test2b)

        # The following example is loosely based on a case from:
        # Lamping 1990, An algorithm for optimal lambda calculus reduction
        # https://dl.acm.org/doi/pdf/10.1145/96709.96711
        # aside from being just a very complicated reduction example, it
        # illustrates a combinatorial blowup (in both time and spaceduring
        # reduction due to the paired function reuse between function and
        # argument. (The full reduction has 512 steps; adding another f and f2
        # gives 5469 steps, etc.)
        # TODO: revisit for optimization
        self.assertEqual(te("(L x_<e,e> : (L f2_<<e,e>,<e,e>> : (f2(f2(f2(f2(x)))))))(L x_e : x)(L f2_<e,e> : (L f_<e,e> : L x_e: f(f(f(f(x)))))(f2))").reduce_all(),
            test2b)

        self.assertEqual(te("((L f_<e,e> : f)((L f_<e,e> : f)((L f_<e,e> : f)(L x_e : x))))(x_e)").reduce_all(),
            self.x)
        self.assertEqual(te("(L g_<e,e> : (L x_e : (L f_<e,e> : (L y_e : g(f(y))))))(L x_e : x)(y_e)(L x_e : x)(x_e)").reduce_all(),
            self.x)
        # nb variable identity in the output may be a bit too strict
        self.assertEqual(te("(L f_<e,e> : f((L x_e : x)(Iota y : (L x_e : P_<e,t>(f(x)))(f(y)))))(L x_e : x)").reduce_all(),
            te("Iota y_e : P_<e,t>(y)"))

    def test_polymorphism(self):
        # geach combinator test
        g = te("L g_<Y,Z> : L f_<X,Y> : L x_X : g(f(x))")
        self.assertEqual(g.try_adjust_type(tp("<<e,t>,<<e,e>,?>>")),
            te("(λ g_<e,t>: (λ f_<e,e>: (λ x_e: g_<e,t>(f_<e,e>(x_e)))))"))

        # note: the choice of variables here is implementation-dependent.
        # TODO: this function should really be testing equivalence under alpha
        # conversion of type vars...
        self.assertEqual(g.let_type(tp("<?,<<<e,t>,?>,?>>")),
            te("(λ g_<Y,Z>: (λ f_<<e,t>,Y>: (λ x_<e,t>: g_<Y,Z>(f_<<e,t>,Y>(x_<e,t>)))))"))
        # z combinator test
        z = te("(λ f_<X,<e,Z>>: (λ g_<e,X>: (λ x_e: f(g(x))(x))))")
        self.assertEqual(z.try_adjust_type(tp("<<e,<e,t>>,?>")),
            te("(λ f_<e,<e,t>>: (λ g_<e,e>: (λ x_e: f_<e,<e,t>>(g_<e,e>(x_e))(x_e))))"))

        # quick check of type inference in lambda expressions
        f = te("L q_X : p_t & f_<Y,Y>(q)")
        self.assertEqual(f[0].type, type_t)
        self.assertEqual(f, te("L q_X : p_t & f_<Y,Y>(q_X)")) # vs hinted q
        self.assertEqual(f, te("L q_X : p_t & f_<Y,Y>(q_∀X)")) # vs ∀ hinted q
        # do the same thing again with a ∀<Y,Y> hint
        f = te("L q_X : p_t & f_∀<Y,Y>(q)")
        self.assertEqual(f[0].type, type_t)
        self.assertEqual(f, te("L q_X : p_t & f_∀<Y,Y>(q_X)")) # vs hinted q
        self.assertEqual(f, te("L q_X : p_t & f_∀<Y,Y>(q_∀X)")) # vs ∀ hinted q

    def test_typenv(self):
        # validate some basic facts about TypeEnv term mappings
        env = core.TypeEnv()
        env.add_term_mapping("x", tp("X"))
        env.add_term_mapping("x", tp("∀X"))
        self.assertEqual(env.term_type('x'), tp('X'))
        self.assertEqual(env.term_type('x', specific=False), tp('∀X'))

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("X"))
        env.add_term_mapping("x", tp("∀<Y,X>"))
        self.assertFalse(env.term_type('x').is_let_polymorphic()) # should be completely fresh
        self.assertEqual(env.term_type('x'), env.type_mapping[tp("X")])

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("∀<<X,<Y,Z>>,t>"))
        env.add_term_mapping("x", tp("∀<<e,<X,Y>>,t>"))
        env.add_term_mapping("x", tp("∀<<Y,<X,e>>,t>"))
        self.assertEqual(env.term_type('x'), tp("∀<<X,<Y,Z>>,t>"))
        self.assertEqual(len(env.term_mapping['x'].specializations), 2)

        env = lamb.meta.core.TypeEnv()
        env.add_term_mapping("x", tp("∀<<e,<X,Y>>,t>"))
        self.assertRaises(TypeMismatch,
            env.add_term_mapping, "x", tp("∀<<Y,<X,e>>,t>"))

    def test_let_polymorphism(self):
        # introduced variable names are implementation dependent

        # basic function+arg cases
        self.assertEqual(te("P_∀<Y,Z>(x_∀X)"), te("P_<X,X1>(x_X)"))
        self.assertEqual(te("P_∀<Y,Z>(x_∀X)"), te("P_<∀Y,∀Z>(x_∀X)"))
        self.assertEqual(te("f_∀<Y,Z>(y_X)"), te("f_<X,∀X>(y_X)"))
        self.assertEqual(te("P_<Y,Z>(x_∀X)"), te("P_<Y,Z>(x_Y)"))
        self.assertEqual(te("P_<Y,∀Z>(x_∀X)"), te("P_<Y,∀X>(x_Y)"))
        self.assertEqual(te("P_<∀Y,Z>(x_∀X)"), te("P_<∀X,Z>(x_∀X)")) # XX is this actually right?

        # various more complicated things
        self.assertEqual(te('L q_X : p_t & f_∀<Y,Y>(q)'), te('λ q_t: (p_t & f_<t,t>(q_t))'))
        self.assertEqual(te("L x_∀X : P_∀<Y,Z>(x)"), te("λ x_X: P_<X,X1>(x_X)"))

        # XX this case infers an expression whose repr would undergo further
        # inference on parsing -- bad! The primary polymorphic type needs to
        # be expressed somehow...
        # self.assertEqual(te("P_∀<Y,Z>(x_∀X) & Q_<∀<X,Y>,t>(x_∀X)"),
        #                  te("P_<X,t>(x_X) & Q_<<X1,X2>,t>(x_<X1,X2>)"))

        self.assertEqual(te("L x_X : P_∀<Y,Z>(x) & Q_<∀<X,Y>,t>(x)"),
                         te("λ x_<X,X1>: (P_<<X,X1>,t>(x_<X,X1>) & Q_<<X,X1>,t>(x_<X,X1>))"))

        f = te("L x_∀X : P_∀<Y,Z>(x) & Q_<∀<X,Y>,t>(x)")
        # weird case: currently the canonical form of this fun doesn't fully
        # express the type constraint
        self.assertEqual(f, te("λ x_∀X: (P_<X,t>(x_X) & Q_<<X1,X2>,t>(x_<X1,X2>))"))
        self.assertEqual(f(te("x_<e,t>")).simplify_all(reduce=True),
                         te("P_<<e,t>,t>(x_<e,t>) & Q_<<e,t>,t>(x_<e,t>)"))
        # however, it is fully enforced on application (even without reduction):
        self.assertRaises(TypeMismatch, f, te("x_e"))

        # a case of unresolvable polymorphism; a primary polymorphic type can't
        # be inferred:
        self.assertRaises(TypeMismatch, te, "P_∀<<e,<X,Y>>,t>(x_Z) & P_∀<<Y,<X,e>>,t>(x_Z)")

    def test_boolean_simplify(self):
        # negation
        testsimp(self, te("~False"), True)
        testsimp(self, te("~True"), False)
        testsimp(self, te("~~True"), True, all=True)
        testsimp(self, te("~~False"), False, all=True)
        testsimp(self, te("~p_t"), te("~p_t"))
        testsimp(self, te("~~p_t"), te("p_t"))
        testsimp(self, te("~~~p_t"), te("~p_t"))
        testsimp(self, te("~~~~p_t"), te("p_t"), all=True)

        # conjunction
        testsimp(self, te("True & True"), True)
        testsimp(self, te("True & False"), False)
        testsimp(self, te("False & True"), False)
        testsimp(self, te("False & False"), False)
        testsimp(self, te("False & p_t"), False)
        testsimp(self, te("p_t & False"), False)
        testsimp(self, te("True & p_t"), te("p_t"))
        testsimp(self, te("p_t & True"), te("p_t"))
        testsimp(self, te("p_t & p_t"), te("p_t"))
        testsimp(self, te("p_t & q_t"), te("p_t & q_t"))
        testsimp(self, te("p_t & ~p_t"), False)

        # disjunction
        testsimp(self, te("True | True"), True)
        testsimp(self, te("True | False"), True)
        testsimp(self, te("False | True"), True)
        testsimp(self, te("False | False"), False)
        testsimp(self, te("False | p_t"), te("p_t"))
        testsimp(self, te("p_t | False"), te("p_t"))
        testsimp(self, te("True | p_t"), True)
        testsimp(self, te("p_t | True"), True)
        testsimp(self, te("p_t | p_t"), te("p_t"))
        testsimp(self, te("p_t | q_t"), te("p_t | q_t"))
        testsimp(self, te("p_t | ~p_t"), True)

        # arrow
        testsimp(self, te("True >> True"), True)
        testsimp(self, te("True >> False"), False)
        testsimp(self, te("False >> True"), True)
        testsimp(self, te("False >> False"), True)
        testsimp(self, te("False >> p_t"), True)
        testsimp(self, te("p_t >> False"), te("~p_t"))
        testsimp(self, te("True >> p_t"), te("p_t"))
        testsimp(self, te("p_t >> True"), True)
        testsimp(self, te("p_t >> p_t"), True)
        testsimp(self, te("p_t >> q_t"), te("p_t >> q_t"))

        # biconditional
        testsimp(self, te("True <=> True"), True)
        testsimp(self, te("True <=> False"), False)
        testsimp(self, te("False <=> True"), False)
        testsimp(self, te("False <=> False"), True)
        testsimp(self, te("False <=> p_t"), te("~p_t"))
        testsimp(self, te("p_t <=> False"), te("~p_t"))
        testsimp(self, te("True <=> p_t"), te("p_t"))
        testsimp(self, te("p_t <=> True"), te("p_t"))
        testsimp(self, te("p_t <=> q_t"), te("p_t <=> q_t"))
        testsimp(self, te("p_t <=> p_t"), True)

        # neq
        testsimp(self, te("True =/= True"), False)
        testsimp(self, te("True =/= False"), True)
        testsimp(self, te("False =/= True"), True)
        testsimp(self, te("False =/= False"), False)
        testsimp(self, te("False =/= p_t"), te("p_t"))
        testsimp(self, te("p_t =/= False"), te("p_t"))
        testsimp(self, te("True =/= p_t"), te("~p_t"))
        testsimp(self, te("p_t =/= True"), te("~p_t"))
        testsimp(self, te("p_t =/= q_t"), te("p_t =/= q_t"))
        testsimp(self, te("p_t =/= p_t"), False)

        # interactions (not exhaustive)
        testsimp(self, te("p_t & ~~p_t"), te("p_t"), all=True)
        testsimp(self, te("~p_t & ~~~p_t"), te("~p_t"), all=True)
        testsimp(self, te("p_t | ~~p_t"), te("p_t"), all=True)
        testsimp(self, te("~p_t | ~~~p_t"), te("~p_t"), all=True)
        testsimp(self, te("p_t => ~~p_t"), True, all=True)
        testsimp(self, te("p_t & ~~~p_t"), False, all=True)

        # normalize term order (and consequent simplification):
        # XX more tests for this
        self.assertEqual(alphanorm(te("q_t & (p_t & ~p_t)")),
                                   te("p_t & ~p_t & q_t"))
        testsimp(self, te("(q_t & p_t) & ~p_t"), False, all=True)
        testsimp(self, te("p_t & q_t & ~~p_t"), te("p_t & q_t"), all=True)
        testsimp(self, te("p_t & q_t | q_t & p_t"), te("p_t & q_t"), all=True)

        # In principle you could add all sorts of other patterns, e.g.
        # conversion of material implication to |, de morgan's laws, etc.
        # testsimp(self, te("~p_t => p_t"), te("p_t"), all=True)
        # under negation normal form:
        # testsimp(self, te("~(p_t & q_t)"), te("~p_t | ~p_t"), all=True)
        # etc..

    def test_quantifier_simp(self):
        # XX more
        testsimp(self, te("Forall y_e : Forall x_e : ~~P_<(e,e),t>(y,x)"),
                       te("Forall x_e : Forall y_e : P_<(e,e),t>(y,x)"),
                       all=True)

    def test_boolean_evaluation(self):
        # this test is more to ensure that this code isn't crashing, than a
        # deep test of boolean inference.
        meta.truthtable(te("False & True"))
        meta.truthtable(te("p_t & q_t & ~p_t"))
        meta.truthtable(te("p_t & q_t & P_<e,t>(x_e)"))
        meta.extract_boolean(te("p4_t & Q_<X,t>(x_X)"),
                                    te("p2_t & Q_<Y,t>(x_Y) | p4_t & ~P_<e,t>(x_e)"))
        self.assertEqual(
            meta.truthtable(te("p_t & q_t")),
            meta.truthtable(te("~(~p_t | ~q_t)")))
        self.assertEqual(
            meta.truthtable(te("False")),
            meta.truthtable(te("False & True")))
        # TODO: generalize to cases where term set is not the same
        # self.assertEqual(
        #     meta.truthtable(te("False")),
        #     meta.truthtable(te("p & ~p"), simplify=False))
        self.assertTrue(meta.truthtable_equiv(
            te("~(p_t & P_<e,t>(x_e) & q_t)"),
            te("~P_<e,t>(x_e) | ~(p_t & q_t)")))

    def test_simplify(self):
        # test a few non-boolean equality cases. (These also exercise set/tuple
        # parsing cases that aren't otherwise tested here)
        self.assertTrue(TypedExpr.factory("{x_e, y_e} <=> {x_e, y_e}").simplify())
        self.assertTrue(TypedExpr.factory("(x_e, y_e) <=> (x_e, y_e)").simplify())

    def test_set_simplify(self):
        for i in range(100):
            x = random_expr(options=RType.SET_RELATION, depth=3)
            try:
                x.simplify_all(eliminate_sets=True, reduce=True)
            except:
                print(f"Failure on depth 3 expression '{repr(x)}'")
                raise

    def test_random_reduce(self):
        # XX the functions generated this way do reduce substantially, but it's
        # not entirely clear to me that they're fully exercising the reduction
        # code...
        arg = te("Test_e")
        for i in range(200):
            f = random_expr(options=RType.LFUN_BOUND, depth=4, typ=tp("<e,e>"))
            x = f(arg).reduce_all()
            self.assertFalse(x.subreducible(use_cache=False),
                f"Reduction failure on random function `{repr(f)}`)")

        arg = te("L x_e : x")
        for i in range(200):
            f = random_expr(options=RType.LFUN_BOUND, depth=4, typ=tp("<<e,e>,e>"))
            x = f(arg).reduce_all()
            self.assertFalse(x.subreducible(use_cache=False),
                f"Reduction failure on random function `{repr(f)}`)")


    # each of these generates 1000 random expressions with the specified depth,
    # and checks whether their repr parses as equal to the original expression
    def test_repr_parse_0(self): test_repr_parse_abstract(self, 0)
    def test_repr_parse_1(self): test_repr_parse_abstract(self, 1)
    def test_repr_parse_2(self): test_repr_parse_abstract(self, 2)
    # def test_repr_parse_3(self): test_repr_parse_abstract(self, 3)
    # def test_repr_parse_4(self): test_repr_parse_abstract(self, 4)
    # def test_repr_parse_5(self): test_repr_parse_abstract(self, 5)
    # def test_repr_parse_6(self): test_repr_parse_abstract(self, 6)
