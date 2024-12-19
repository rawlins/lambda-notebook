import logging, unittest, random, enum, math
import collections.abc
import lamb
from lamb import types, parsing
from lamb.types import TypeMismatch, type_e, type_t, type_n
from . import core, boolean, number, sets, meta, quantifiers
from .core import logger, te, tp, get_type_system, TypedExpr, LFun, TypedTerm
from .core import is_concrete, is_te
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
    options = [quantifiers.Forall, quantifiers.Exists, quantifiers.ExistsExact]
    op_class = random.choice(options)
    return op_class.random(ctrl, max_type_depth)


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


def random_tf_op_expr(ctrl_fun):
    op = random.choice(core.registry.get_operators(type_t, type_t, exact=True))
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

def random_from_class(cls, max_depth=1, used_vars=None, ctrl=None):
    global random_used_vars
    if used_vars is None:
        used_vars = set()
    random_used_vars = used_vars

    def def_ctrl(**args):
        global random_used_vars
        return random_expr(depth=max_depth-1, used_vars=random_used_vars,
                                                                    **args)

    if ctrl is None:
        ctrl = def_ctrl
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

random_types = [type_t]

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

def testsimp(self, a, b, all=False, exec=False, **kwargs):
    if exec:
        all = True
    if all:
        intermediate = a.simplify_all(**kwargs)
    else:
        intermediate = a.simplify(**kwargs)
    teb = te(b)
    self.assertEqual(intermediate, teb,
                f"Failed simplification test: '{repr(a)} == {repr(b)}' (got {repr(intermediate)})")
    if exec:
        execed_a = meta.exec(a)
        execed_b = meta.exec(teb)
        self.assertEqual(execed_a, execed_b,
                f"Failed exec test: '{repr(a)} == {repr(b)}' (got `{repr(execed_a)}` == `{repr(execed_b)}`)")
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
              quantifiers.Forall,
              quantifiers.Exists,
              quantifiers.ExistsExact,
              quantifiers.Iota,
              quantifiers.IotaPartial,
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
        core.set_strict_type_parsing()
        self.ident = te("L x_e : x") 
        self.ia = TypedExpr.factory(self.ident, "y_e")
        self.ib = LFun(TypedTerm("y", typ=type_e), self.ia)
        self.P = TypedTerm("P", types.FunType(type_e, type_t))
        self.Q = TypedTerm("Q", types.FunType(type_e, type_t))
        self.x = TypedTerm("x", type_e)
        self.y = TypedTerm("y", type_e)
        self.t = TypedExpr.factory(self.P, self.x)
        self.t2 = TypedExpr.factory(self.Q, self.x)
        self.body = TypedExpr.factory("&", self.t, self.t) | self.t
        self.p = TypedTerm("p", type_t)
        self.testf = LFun(TypedTerm("x", typ=type_e), self.body)

    def tearDown(self):
        # other tests may want this, but let them decide
        core.set_strict_type_parsing(False)

    def test_basic(self):
        # equality basics
        self.assertEqual(self.P, self.P)
        self.assertEqual(self.x, self.x)
        self.assertEqual(self.testf, self.testf)
        self.assertNotEqual(self.P, self.Q)
        self.assertNotEqual(self.x, self.y)

    def test_op_resolution(self):
        # use resolution of <=> as a basic test case for operator resolution
        # with polymorphism. We have:
        #     core.BinaryGenericEqExpr for type (X,X)
        #     sets.SetEquivalence for type ({X},{X})
        #     boolean.BinaryBiarrowExpr for type (t,t)
        self.assertTrue(isinstance(te("x_X <=> y_Y"), core.BinaryGenericEqExpr))
        self.assertTrue(isinstance(te("x_n <=> y_n"), core.BinaryGenericEqExpr))
        self.assertTrue(isinstance(te("x_X <=> y_n"), core.BinaryGenericEqExpr))
        self.assertTrue(isinstance(te("x_X <=> y_t"), boolean.BinaryBiarrowExpr))
        self.assertTrue(isinstance(te("x_t <=> y_Y"), boolean.BinaryBiarrowExpr))
        self.assertTrue(isinstance(te("x_t <=> y_t"), boolean.BinaryBiarrowExpr))
        self.assertTrue(isinstance(te("x_{X} <=> y_Y"), sets.SetEquivalence))
        self.assertTrue(isinstance(te("x_X <=> y_{Y}"), sets.SetEquivalence))
        self.assertTrue(isinstance(te("x_{X} <=> y_{Y}"), sets.SetEquivalence))
        self.assertTrue(isinstance(te("x_{e} <=> y_{Y}"), sets.SetEquivalence))
        self.assertTrue(isinstance(te("x_{X} <=> y_{e}"), sets.SetEquivalence))
        self.assertTrue(isinstance(te("x_{e} <=> y_{e}"), sets.SetEquivalence))

    def test_class_random(self):
        for c in te_classes:
            for i in range(100):
                x = random_from_class(c, max_depth=2)
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

    def test_binding_random(self):
        for i in range(1,3):
            for j in range(100):
                x = random_expr(options=RType.BINDING_EXPR, depth=i)
                try:
                    x.simplify_all()
                    x.simplify_all(eliminate_quantifiers=True)
                except:
                    print(f"simplification failure on binding expression `{repr(x)}`")
                    raise

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
        core.set_strict_type_parsing(False)
        try:
            te("L x: L y: In(y)(x)")
        finally:
            core.set_strict_type_parsing(True)
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

    def test_binary_ops(self):
        # this test exercises python versions of overloaded binary operators
        # in an exhaustive way, verifying:
        # * that both orders work with two TypedExprs
        # * that both orders work with one TypedExpr and one python element
        # * that order is preserved in the latter case where possible (it
        #   is not possible for comparison relations)
        # the only binary operator that isn't tested here at all is SetContains
        # tests are at types n, t, and {n}
        numeric = ["+", "-", "*", "/", "**", "%"]
        numeric_rels = ["%", "<=", ">=", "<", ">"]
        locals = {'e': te("3"), 'e2': te("x_n")}
        for op in numeric:
            # note that `%` is currently tested here; so the output type is
            # homogenous
            for order in (f"2 {op} e", f"e {op} 2"):
                self.assertTrue(is_te(eval(order, None, locals)),
                    f"`{order}` is not a TypedExpr")
            check = 0
            for order in (f"2 {op} e2", f"e2 {op} 2"):
                self.assertTrue(eval(order, None, locals)[check].meta(),
                    f"Swapped order for `{order}`")
                check += 1

        for op in numeric_rels:
            for order in (f"2 {op} e2", f"e2 {op} 2", f"2 {op} e2", f"e2 {op} 2"):
                # we are just checking for errors here, really. It isn't
                # possible to get the order right in a general way; see notes
                # on this in the __r*__ implementations in core.
                self.assertTrue(is_te(eval(order, None, locals)),
                    f"`{order}` is not a TypedExpr")

        boolean = ["&", "|", "%", ">>", "^"]
        locals = {'e': te("True"), 'e2': te("x_t")}
        for op in boolean:
            for order in (f"True {op} e", f"e {op} True"):
                self.assertTrue(is_te(eval(order, None, locals)),
                    f"`{order}` is not a TypedExpr")
            check = 0
            for order in (f"True {op} e2", f"e2 {op} True"):
                self.assertTrue(eval(order, None, locals)[check].meta(),
                    f"Swapped order for `{order}`")
                check += 1

        sets = ["&", "|", "-", "%"]
        # SetContains not tested here
        set_rels = ["%", "<=", ">=", "<", ">"]
        locals = {'e': te("{3}"), 'e2': te("x_{n}")}
        for op in sets:
            # note that `%` is currently tested here; so the output type is
            # homogenous
            for order in (f"{{2}} {op} e", f"e {op} {{2}}"):
                self.assertTrue(is_te(eval(order, None, locals)),
                    f"`{order}` is not a TypedExpr")
            check = 0
            for order in (f"{{2}} {op} e2", f"e2 {op} {{2}}"):
                self.assertTrue(eval(order, None, locals)[check][0].meta(),
                    f"Swapped order for `{order}`")
                check += 1

        for op in set_rels:
            for order in (f"{{2}} {op} e2", f"e2 {op} {{2}}", f"{{2}} {op} e2", f"e2 {op} {{2}}"):
                # we are just checking for errors here, really. It isn't
                # possible to get the order right in a general way; see notes
                # on this in the __r*__ implementations in core.
                self.assertTrue(is_te(eval(order, None, locals)),
                    f"`{order}` is not a TypedExpr")


    def test_eq(self):
        # XX this could cover quite a bit more ground
        t1 = te("(_c1, _c2, (True, False))")
        meta_t1 = MetaTerm(('_c1', '_c2', (True, False)))
        t2 = te("(_c1, _c2, (True, True))")
        meta_t2 = MetaTerm(('_c1', '_c2', (True, True)))
        testsimp(self, t1.equivalent_to(t1), True, exec=True)
        testsimp(self, t1.equivalent_to(meta_t1), True, exec=True)
        testsimp(self, meta_t1.equivalent_to(t1), True, exec=True)
        testsimp(self, meta_t1.equivalent_to(meta_t1), True, exec=True)
        testsimp(self, t1.equivalent_to(t2), False, exec=True)
        testsimp(self, t1.equivalent_to(meta_t2), False, exec=True)
        testsimp(self, meta_t1.equivalent_to(t2), False, exec=True)
        testsimp(self, meta_t1.equivalent_to(meta_t2), False, exec=True)
        s1 = te("{{_c1, _c2}, {_c3}}")
        meta_s1 = meta.MetaTerm(frozenset({frozenset({'_c2', '_c1'}), frozenset({'_c3'})}))
        testsimp(self, s1.equivalent_to(s1), True, exec=True)
        testsimp(self, s1.equivalent_to(meta_s1), True, exec=True)
        testsimp(self, meta_s1.equivalent_to(s1), True, exec=True)
        testsimp(self, meta_s1.equivalent_to(meta_s1), True, exec=True)
        # not exactly eq, but close enough
        elem = te("{_c1, _c2}")
        meta_elem = meta.MetaTerm(frozenset({'_c2', '_c1'}))
        testsimp(self, s1[0] << s1, True, exec=True)
        testsimp(self, s1[0] << meta_s1, True, exec=True)
        testsimp(self, meta_elem << s1, True, exec=True)
        testsimp(self, meta_elem << meta_s1, True, exec=True)
        testsimp(self, elem << s1, True, exec=True)
        testsimp(self, elem << meta_s1, True, exec=True)

        with tp("e").restrict_domain(count=4):
            # these are chosen to avoid certain optimizations involved in <<
            # and exercise some of the more general code
            s1 = te("(Set x_{e} : x << {{_c1}})")
            s2 = te("(Set x_{e} : _c1 << x & x <=> {_c1})")
            s3 = te("(Set x_{e} : _c1 << x & x <=> {_c1, _c2})")
            testsimp(self, s1.equivalent_to(s2), True, exec=True, eliminate_sets=True)
            testsimp(self, s1.equivalent_to(s3), False, exec=True, eliminate_sets=True)

    def test_reduce(self):
        self.assertEqual(self.ident(self.y).reduce(), self.y)

        # test: when a free variable in a function scopes under an operator, do
        # not bind the variable on application        
        pmw_test1 = LFun(TypedTerm("p", typ=type_t),
                        LFun(TypedTerm("x", typ=type_e), self.t & self.p))
        pmw_test1b = LFun(TypedTerm("x", typ=type_e), self.t & self.t2)
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
        self.assertEqual(te("(L f_<e,e> : f((L x_e : x)(Iota y_e : (L x_e : P_<e,t>(f(x)))(f(y)))))(L x_e : x)").reduce_all(),
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
        env.add_term_mapping("x", tp("∀X"), allow_poly=False)
        env.add_term_mapping("x", tp("∀Y"))
        self.assertEqual(env.term_type('x'), tp('∀X'))
        self.assertEqual(env.term_type('x', specific=False), tp('∀X'))
        env.add_term_mapping("x", tp("X"))
        self.assertEqual(env.term_type('x'), tp('X'))
        self.assertEqual(env.term_type('x', specific=False), tp('X'))

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("∀X"), allow_poly=True)
        env.add_term_mapping("x", tp("∀Y"))
        self.assertEqual(env.term_type('x'), tp('∀X'))
        env.add_term_mapping("x", tp("X"))
        self.assertEqual(env.term_type('x'), tp('X'))
        self.assertEqual(env.term_type('x', specific=False), tp('∀X'))

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("X"))
        env.add_term_mapping("x", tp("∀X"), allow_poly=True)
        self.assertEqual(env.term_type('x'), tp('X'))
        self.assertEqual(env.term_type('x', specific=False), tp('∀X'))

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("X"))
        env.add_term_mapping("x", tp("∀<Y,X>"), allow_poly=True)
        self.assertFalse(env.term_type('x').is_let_polymorphic()) # should be completely fresh
        self.assertEqual(env.term_type('x'), env.type_mapping[tp("X")])

        env = core.TypeEnv()
        env.add_term_mapping("x", tp("∀<<X,<Y,Z>>,t>"), allow_poly=True)
        env.add_term_mapping("x", tp("∀<<e,<X,Y>>,t>"))
        env.add_term_mapping("x", tp("∀<<Y,<X,e>>,t>"))
        self.assertEqual(env.term_type('x'), tp("∀<<X,<Y,Z>>,t>"))
        self.assertEqual(len(env.term_mapping['x'].specializations), 2)

        env = lamb.meta.core.TypeEnv()
        env.add_term_mapping("x", tp("∀<<e,<X,Y>>,t>"), allow_poly=True)
        # with let-polymorphism, this is a case where we cannot infer
        # a principal polymorphic type in absence of guidance from above:
        self.assertRaises(TypeMismatch,
            env.add_term_mapping, "x", tp("∀<<Y,<X,e>>,t>"))

        env = lamb.meta.core.TypeEnv()
        env.add_term_mapping("x", tp("∀<<e,<X,Y>>,t>"), allow_poly=False)
        env.add_term_mapping("x", tp("∀<<Y,<X,e>>,t>"))
        # without let-polymorphism, these two straightforwardly have a principal
        # type:
        self.assertEqual(env.term_type('x'), tp("∀<<e,<X,e>>,t>"))

        # test the interaction of an inferred type mapping during parsing, and
        # an externally imposed type assignment. Note that this segment requires
        # an unambiguous resolution of >> to work, but that is incidental to
        # what this is testing.
        e1 = (te("P_Z(x_<X,Y>) >> Q_Z2(x_<X1,Y1>)", let=False)
                .under_type_assignment({tp('Y1'):tp('Y'), tp('X1'):tp('X')})
                .regularize_type_env())
        e2 = (te("P_Z(x_<X,Y>) >> Q_Z2(x_<X1,Y1>)", let=False)
                .under_type_assignment({tp('Y'):tp('Y1'), tp('X'):tp('X1')})
                .regularize_type_env())
        self.assertNotEqual(e1, e2)
        self.assertEqual(e1, te("(P_<<X,Y>,t>(x_<X,Y>) >> Q_<<X,Y>,t>(x_<X,Y>))"))
        self.assertEqual(e2, te("(P_<<X1,Y1>,t>(x_<X1,Y1>) >> Q_<<X1,Y1>,t>(x_<X1,Y1>))"))

    def test_let_polymorphism(self):
        # introduced variable names are implementation dependent

        # basic function+arg cases
        self.assertEqual(te("P_∀<Y,Z>(x_∀X)"), te("P_<X,X1>(x_X)"))
        self.assertEqual(te("P_∀<Y,Z>(x_∀X)"), te("P_<∀Y,∀Z>(x_∀X)"))
        self.assertEqual(te("f_∀<Y,Z>(y_X)"), te("f_<X,∀X>(y_X)"))
        self.assertEqual(te("P_<Y,Z>(x_∀X)"), te("P_<Y,Z>(x_Y)"))
        self.assertEqual(te("P_<Y,∀Z>(x_∀X)"), te("P_<Y,∀X>(x_Y)"))
        self.assertEqual(te("P_<∀Y,Z>(x_∀X)"), te("P_<∀X,Z>(x_∀X)")) # XX is this actually right?

        # various more complicated examples
        self.assertEqual(te('L q_X : p_t & f_∀<Y,Y>(q)'), te('λ q_t: (p_t & f_<t,t>(q_t))'))
        self.assertEqual(te("L x_∀X : P_∀<Y,Z>(x)"), te("λ x_X: P_<X,X1>(x_X)"))
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

        # let-polymorphism is disallowed given just local ∀-bound type hints,
        # so a case like the previous without a lambda binder will enforce a
        # single polymorphic type for x:
        self.assertEqual(te("P_∀<Y,Z>(x_∀X) & Q_<∀<X,Y>,t>(x_∀X)"),
                         te("P_<<X,X1>,t>(x_<X,X1>) & Q_<<X,X1>,t>(x_<X,X1>)"))

        # another pair like the above, where different results obtain with and
        # without a binder. In the polymorphic case, `x` is allowed to specialize
        # to completely incompatible types(!):
        self.assertEqual(te("L x_∀X : P_∀<<X,Y>,Z>(x_∀X) & Q_<e,t>(x_∀X)"),
                         te("(λ x_∀X: (P_<<X,X1>,t>(x_<X,X1>) & Q_<e,t>(x_e)))"))

        # and without let-polymorphism a case like this will fail altogether,
        # since Q forces x_e, and P forces an incompatible functional type for
        # x:
        self.assertRaises(TypeMismatch, te, "P_∀<<X,Y>,Z>(x_∀X) & Q_<e,t>(x_∀X)")

        # a case of unresolvable polymorphism; a primary polymorphic type can't
        # be inferred:
        self.assertRaises(parsing.ParseError, te,
                        "L f_∀<<e,<X,Y>>,t>: f(x_Z) & f_∀<<Y,<X,e>>,t>(x_Z)")
        # however, without let polymorphism the body would be completely fine,
        # since there is a straightforward principal type:
        self.assertEqual(te("f_∀<<e,<X,Y>>,t>(x_Z) & f_∀<<Y,<X,e>>,t>(x_Z)"),
                         te("f_<<e,<X,e>>,t>(x_<e,<X,e>>) & f_<<e,<X,e>>,t>(x_<e,<X,e>>)"))

    def test_boolean_simplify(self):
        # negation
        testsimp(self, te("~False"), True, exec=True)
        testsimp(self, te("~True"), False, exec=True)
        testsimp(self, te("~~True"), True, exec=True)
        testsimp(self, te("~~False"), False, exec=True)
        testsimp(self, te("~p_t"), te("~p_t"))
        testsimp(self, te("~~p_t"), te("p_t"))
        testsimp(self, te("~~~p_t"), te("~p_t"))
        testsimp(self, te("~~~~p_t"), te("p_t"), all=True)

        # conjunction
        testsimp(self, te("True & True"), True, exec=True)
        testsimp(self, te("True & False"), False, exec=True)
        testsimp(self, te("False & True"), False, exec=True)
        testsimp(self, te("False & False"), False, exec=True)
        testsimp(self, te("True & True & False"), False, exec=True)
        testsimp(self, te("False & p_t"), False)
        testsimp(self, te("p_t & False"), False)
        testsimp(self, te("True & p_t"), te("p_t"))
        testsimp(self, te("p_t & True"), te("p_t"))
        testsimp(self, te("p_t & p_t"), te("p_t"))
        testsimp(self, te("p_t & q_t"), te("p_t & q_t"))
        testsimp(self, te("p_t & ~p_t"), False)

        # disjunction
        testsimp(self, te("True | True"), True, exec=True)
        testsimp(self, te("True | False"), True, exec=True)
        testsimp(self, te("False | True"), True, exec=True)
        testsimp(self, te("False | False"), False, exec=True)
        testsimp(self, te("False | False | True"), True, exec=True)
        testsimp(self, te("False | p_t"), te("p_t"))
        testsimp(self, te("p_t | False"), te("p_t"))
        testsimp(self, te("True | p_t"), True)
        testsimp(self, te("p_t | True"), True)
        testsimp(self, te("p_t | p_t"), te("p_t"))
        testsimp(self, te("p_t | q_t"), te("p_t | q_t"))
        testsimp(self, te("p_t | ~p_t"), True)

        # arrow
        testsimp(self, te("True >> True"), True, exec=True)
        testsimp(self, te("True >> False"), False, exec=True)
        testsimp(self, te("False >> True"), True, exec=True)
        testsimp(self, te("False >> False"), True, exec=True)
        testsimp(self, te("False >> p_t"), True)
        testsimp(self, te("p_t >> False"), te("~p_t"))
        testsimp(self, te("True >> p_t"), te("p_t"))
        testsimp(self, te("p_t >> True"), True)
        testsimp(self, te("p_t >> p_t"), True)
        testsimp(self, te("p_t >> q_t"), te("p_t >> q_t"))

        # biconditional
        testsimp(self, te("True <=> True"), True, exec=True)
        testsimp(self, te("True <=> False"), False, exec=True)
        testsimp(self, te("False <=> True"), False, exec=True)
        testsimp(self, te("False <=> False"), True, exec=True)
        testsimp(self, te("False <=> p_t"), te("~p_t"))
        testsimp(self, te("p_t <=> False"), te("~p_t"))
        testsimp(self, te("True <=> p_t"), te("p_t"))
        testsimp(self, te("p_t <=> True"), te("p_t"))
        testsimp(self, te("p_t <=> q_t"), te("p_t <=> q_t"))
        testsimp(self, te("p_t <=> p_t"), True)

        # neq
        testsimp(self, te("True =/= True"), False, exec=True)
        testsimp(self, te("True =/= False"), True, exec=True)
        testsimp(self, te("False =/= True"), True, exec=True)
        testsimp(self, te("False =/= False"), False, exec=True)
        testsimp(self, te("False =/= p_t"), te("p_t"))
        testsimp(self, te("p_t =/= False"), te("p_t"))
        testsimp(self, te("True =/= p_t"), te("~p_t"))
        testsimp(self, te("p_t =/= True"), te("~p_t"))
        testsimp(self, te("p_t =/= q_t"), te("p_t =/= q_t"))
        testsimp(self, te("p_t =/= p_t"), False)

        # interactions (not exhaustive)
        testsimp(self, te("True & ~~True"), True, exec=True)
        testsimp(self, te("~True & ~~~True"), te("False"), exec=True)
        testsimp(self, te("True | ~~True"), True, exec=True)
        testsimp(self, te("~True | ~~~True"), False, exec=True)
        testsimp(self, te("True => ~~True"), True, exec=True)
        testsimp(self, te("True & ~~~True"), False, exec=True)
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

        # not a very interesting domain, but these exercise some basic
        # implementational code even extending to multiple quantifiers
        testsimp(self, te("Forall x_t : x"), False, exec=True)
        testsimp(self, te("Forall x_t : ~x"), False, exec=True)
        testsimp(self, te("Forall x_t : ~x | ~~x"), True, exec=True)
        testsimp(self, te("Exists x_t : x"), True, exec=True)
        testsimp(self, te("Exists x_t : ~x"), True, exec=True)
        testsimp(self, te("ExistsExact x_t : x"), True, exec=True)
        testsimp(self, te("ExistsExact x_t : ~x"), True, exec=True)
        testsimp(self, te("ExistsExact x_t : ~x | ~~x"), False, exec=True)
        testsimp(self, te("Iota x_t : x"), True, exec=True)
        testsimp(self, te("Iota x_t : ~x"), False, exec=True)
        # XX simplify doesn't do anything on this case, even though it does
        # on other quantifiers
        self.assertRaises(meta.DomainError, meta.exec, te("Iota x_t : x == x"))

        testsimp(self, te("Forall x_t : Exists y_t : x == y"), True, exec=True)
        testsimp(self, te("Forall x_t : Forall y_t : x == y"), False, exec=True)
        testsimp(self, te("Forall x_t : Forall y_t : Exists z_t: x | y | z"), True, exec=True)
        testsimp(self, te("Forall x_t : Forall y_t : Forall z_t: x | y | z"), False, exec=True)
        testsimp(self, te("Exists x_t : Exists y_t : Exists z_t: x & y & z"), True, exec=True)

        # interesting case that came up in random testing
        testsimp(self, te("(ExistsExact p_t: (Exists n_n: p_t))"), True, exec=True)

    def quant_restrictors(self):
        # validate cardinality checking for binding expressions. These also
        # exercise type domain cardinality code. This code is general across
        # RestrictedBindingOps so it's only tested with one.
        self.assertEqual(te("Forall x_e : P_<e,t>(x)").domain_cardinality(), math.inf)
        self.assertEqual(te("Forall x_e << (Set x_e : True) : P_<e,t>(x)").domain_cardinality(), math.inf)
        self.assertEqual(te("Forall x_e << {}: P_<e,t>(x)").domain_cardinality(), math.inf)
        self.assertEqual(te("Forall x_e << (Set x_e : False): P_<e,t>(x)").domain_cardinality(), math.inf)
        with tp("e").restrict_domain({}):
            self.assertEqual(te("Forall x_e : P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << (Set x_e : True): P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << {}: P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << (Set x_e : False): P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_<e,t> : P_<<e,t>,t>(x)").domain_cardinality(), 1) # the empty function
            self.assertEqual(te("Forall x_{e} : P_<{e},t>(x)").domain_cardinality(), 1) # the empty set
            self.assertEqual(te("Forall x_(e) : P_<(e),t>(x)").domain_cardinality(), 0)
        with tp("e").restrict_domain({'_c1'}):
            self.assertEqual(te("Forall x_e : P_<e,t>(x)").domain_cardinality(), 1)
            self.assertEqual(te("Forall x_e << (Set x_e : True): P_<e,t>(x)").domain_cardinality(), 1)
            self.assertEqual(te("Forall x_e << {}: P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << (Set x_e : False): P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << {_c1}: P_<e,t>(x)").domain_cardinality(), 1)
            self.assertEqual(te("Forall x_<e,t> : P_<<e,t>,t>(x)").domain_cardinality(), 2)
            self.assertEqual(te("Forall x_{e} : P_<{e},t>(x)").domain_cardinality(), 2)
            self.assertEqual(te("Forall x_(e) : P_<(e),t>(x)").domain_cardinality(), 1)
        with tp("e").restrict_domain({'_c1', '_c2'}):
            self.assertEqual(te("Forall x_e : P_<e,t>(x)").domain_cardinality(), 2)
            self.assertEqual(te("Forall x_e << (Set x_e : True): P_<e,t>(x)").domain_cardinality(), 2)
            self.assertEqual(te("Forall x_e << {}: P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << (Set x_e : False): P_<e,t>(x)").domain_cardinality(), 0)
            self.assertEqual(te("Forall x_e << {_c1}: P_<e,t>(x)").domain_cardinality(), 1)
            self.assertEqual(te("Forall x_<e,t> : P_<<e,t>,t>(x)").domain_cardinality(), 4)
            self.assertEqual(te("Forall x_{e} : P_<{e},t>(x)").domain_cardinality(), 4)
            self.assertEqual(te("Forall x_(e) : P_<(e),t>(x)").domain_cardinality(), 2)

        # validate trivial body cases
        testsimp(self, te("Forall x_e << {} : True"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1} : True"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1, _c2} : True"), True, exec=True)
        testsimp(self, te("Forall x_e << {} : False"), False, exec=True)
        testsimp(self, te("Forall x_e << {_c1} : False"), False, exec=True)
        testsimp(self, te("Forall x_e << {_c1, _c2} : False"), False, exec=True)
        testsimp(self, te("Exists x_e << {} : True"), False, exec=True)
        testsimp(self, te("Exists x_e << {_c1} : True"), True, exec=True)
        testsimp(self, te("Exists x_e << {_c1, _c2} : True"), True, exec=True)
        testsimp(self, te("Exists x_e << {} : False"), False, exec=True)
        testsimp(self, te("Exists x_e << {_c1} : False"), False, exec=True)
        testsimp(self, te("Exists x_e << {_c1, _c2} : False"), False, exec=True)

        # basic test of non-trivial bodies
        testsimp(self, te("Forall x_e << {} : x == _c1"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1} : x == _c1"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1} : x == _c1 | x == _c2"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1, _c2} : x == _c1"), False, exec=True)
        testsimp(self, te("Exists x_e << {} : x == _c1"), False, exec=True)
        testsimp(self, te("Exists x_e << {_c1} : x == _c1"), True, exec=True)
        testsimp(self, te("Exists x_e << {_c1} : x == _c1 | x == _c2"), True, exec=True)
        testsimp(self, te("Exists x_e << {_c1, _c2} : x == _c1"), True, exec=True)
        testsimp(self, te("ExistsExact x_e << {} : x == _c1"), False, exec=True)
        testsimp(self, te("ExistsExact x_e << {_c1} : x == _c1"), True, exec=True)
        testsimp(self, te("ExistsExact x_e << {_c1, _c2} : x == _c1"), False, exec=True)
        self.assertRaises(meta.DomainError, te("Iota x_e << {} : x == _c1").simplify_all)
        self.assertRaises(meta.DomainError, meta.exec, te("ExistsExact x_e << {} : x == _c1"))
        testsimp(self, te("Iota x_e << {_c1} : x == _c1"), te("_c1"), exec=True)
        testsimp(self, te("Iota x_e << {_c1, _c2} : x == _c1"), te("_c1"), exec=True)
        testsimp(self, te("Iota x_e << {_c1} : x == _c1 | x == _c2"), te("_c1"), exec=True)
        self.assertRaises(meta.DomainError, te("Iota x_e << {_c1, _c2} : x == _c1 | x == _c2").simplify_all)
        self.assertRaises(meta.DomainError, meta.exec, te("Iota x_e << {_c1, _c2} : x == _c1 | x == _c2"))

        # cardinality 1 elimination (simplification-specific)
        testsimp(self, te("Forall x_e << {_c1} : P_<e,t>(x)"), te("P_<e,t>(_c1)"), all=True)
        testsimp(self, te("Exists x_e << {_c1} : P_<e,t>(x)"), te("P_<e,t>(_c1)"), all=True)
        testsimp(self, te("ExistsExact x_e << {_c1} : P_<e,t>(x)"), te("P_<e,t>(_c1)"), all=True)
        testsimp(self, te("Forall x_e << {C_e} : P_<e,t>(x)"), te("P_<e,t>(C_e)"), all=True)
        testsimp(self, te("Exists x_e << {C_e} : P_<e,t>(x)"), te("P_<e,t>(C_e)"), all=True)
        testsimp(self, te("ExistsExact x_e << {C_e} : P_<e,t>(x)"), te("P_<e,t>(C_e)"), all=True)

        # a few doubly quantified cases
        testsimp(self, te("Forall x_e << {_c1, _c2, _c3} : Exists y_e  << {_c1, _c2, _c3} : x == y"), True, exec=True)
        testsimp(self, te("Forall x_e << {_c1, _c2, _c3} : Forall y_e  << {_c1, _c2, _c3} : x == y"), False, exec=True)

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
        testsimp(self, te("{x_e, y_e} <=> {x_e, y_e}"), True, all=True)
        testsimp(self, te("{x_e, y_e} <=> {y_e, x_e}"), True, all=True)
        testsimp(self, te("(x_e, y_e) <=> (x_e, y_e)"), True, all=True)
        # should not simplify:
        testsimp(self, te("(x_e, y_e) <=> (y_e, x_e)"), te("(x_e, y_e) <=> (y_e, x_e)"), all=True)

        # execable equality cases:
        testsimp(self, te("{True, False} <=> {True, False, True}"), True, exec=True)
        testsimp(self, te("{_c1, _c3} <=> {_c1, _c3, _c1}"), True, exec=True)
        testsimp(self, te("(_c1, _c3) <=> (_c1, _c3)"), True, exec=True)
        # XX simplify does not handle these correctly
        # testsimp(self, te("(_c1, _c3) <=> (_c3, _c1)"), False, exec=True)
        # testsimp(self, te("~((_c1, _c3) <=> (_c3, _c1))"), True, exec=True)
        self.assertFalse(meta.exec(te("(_c1, _c3) <=> (_c3, _c1)")))
        self.assertTrue(meta.exec(te("~((_c1, _c3) <=> (_c3, _c1))")))

    def test_exec(self):
        # see also, `testsimp` calls with exec=True
        # XX generate random exec-safe expressions? it would be ideal to test
        # all metalanguage ops

        # really basic cases:
        self.assertTrue(meta.exec(te("p_t & q_t"), p=True, q=True))
        self.assertTrue(meta.exec(te("L p_t : p_t & q_t"), q=True)(True))
        self.assertFalse(meta.exec(te("L p_t : p_t & q_t"), q=True)(False))
        self.assertRaises(TypeError, meta.exec, te("p_t & q_t")) # missing context

        te_f = te("L x_e: x == _c1")
        f = meta.exec(te_f)
        self.assertTrue(f('_c1'))
        self.assertFalse(f('_c2'))
        with types.type_e.restrict_domain({'c0', 'c1','c2', 'c3'}):
            self.assertRaises(TypeError, meta.exec, te("ExistsExact x_e : P_<e,t>(x)"))
            self.assertTrue(meta.exec(te("ExistsExact x_e : P_<e,t>(x)"), P=f))
            self.assertTrue(meta.exec(te("ExistsExact x_e : P_<e,t>(x)"), P=te_f))
            self.assertTrue(meta.exec(te("L f_<e,t> : ExistsExact x_e : f_<e,t>(x)"))(f))
            self.assertTrue(meta.exec(te("L f_<e,t> : ExistsExact x_e : f_<e,t>(x)"))(te_f))
            self.assertTrue(meta.exec(te("L f_<e,t> : ~(ExistsExact x_e : ~f_<e,t>(x))"))(f))

            # exercise set code...several of these cases should in principle be
            # handleable by simplify as well
            s1 = te("Set x_e : x << {_c1, _c2}")
            s2 = te("Set x_e : ~(x == _c1)")
            s3 = te("{_c1, _c2, _c3}")
            s4 = te("{_c0, _c2, _c3}")
            s5 = te({'_c2', '_c3'})
            self.assertTrue(meta.exec(((s3 - s4) | s3).equivalent_to(s3)))
            self.assertFalse(meta.exec(((s3 - s4) | s3).equivalent_to(s4)))
            self.assertTrue(meta.exec((s1 & s2).equivalent_to(te({'_c2'}))))
            self.assertTrue(meta.exec((s2 & s4).equivalent_to(s4)))
            self.assertTrue(meta.exec((s2 & s3).equivalent_to(s5)))
            self.assertTrue(meta.exec((s2 & s3) <= s5))
            self.assertTrue(meta.exec((s2 & s3) >= s5))
            self.assertFalse(meta.exec((s2 & s3) < s5))
            self.assertFalse(meta.exec((s2 & s3) > s5))
            self.assertTrue(meta.exec((s2 - s3) < s4))
            self.assertTrue(meta.exec(s5 <= s3))
            self.assertTrue(meta.exec(s5 < s3))
            self.assertTrue(meta.exec(s5 < s2))
            self.assertTrue(meta.exec((s1 & s2) <= s5))
            self.assertTrue(meta.exec((s1 & s2) < s5))
            self.assertFalse(meta.exec((s1 & s2) > s5))

        # test some aspects of the wrapper api
        f = te("L s_{{e}} : L x_e : L y_e : ({x} << s) >> ({y} << s)")
        # can't directly write recursive sets in python, use a factory
        s = sets.sset([{'_c1', '_c2'}, {'_c1'}, {'_c2'}])
        self.assertTrue(meta.exec(f, s, te("_c1"), te("_c2")))
        self.assertTrue(meta.exec(f, s, te("_c3"), te("_c1")))
        self.assertFalse(meta.exec(f, s, te("_c1"), te("_c3")))
        self.assertTrue(meta.exec(f, s, te("_c3"))(te("_c1")))
        self.assertFalse(meta.exec(f, s, te("_c1"))(te("_c3")))
        self.assertTrue(meta.exec(f, s)(te("_c3"))(te("_c1")))
        self.assertFalse(meta.exec(f, s)(te("_c1"))(te("_c3")))
        self.assertTrue(meta.exec(f)(s)(te("_c3"))(te("_c1")))
        self.assertFalse(meta.exec(f)(s)(te("_c1"))(te("_c3")))
        self.assertRaises(TypeError, meta.exec(f), te("_c1"))
        self.assertRaises(TypeError, meta.exec(f)(s), 1)
        self.assertRaises(TypeError, meta.exec(f, s), 1)
        self.assertTrue(meta.exec(f, _uncurry=True)(s, te("_c3"), te("_c1")))
        self.assertFalse(meta.exec(f, _uncurry=True)(s, te("_c1"), te("_c3")))
        self.assertRaises(TypeError, meta.exec(f, _uncurry=True), s)
        self.assertRaises(TypeError, meta.exec(f, _uncurry=True), s, te("_c3"))
        self.assertRaises(TypeError, meta.exec(f, _uncurry=True), te("_c3"), s, te("_c1"))
        self.assertRaises(TypeError, meta.exec(f, _uncurry=True), s, te("_c3"), te("_c1"), te("_c1"))

        # a few more error cases that fail arity or dynamic type checks
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : p_t & q_t"), q=True),
            1) # dynamic type check on p (bool vs number)
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : L q_t : p_t & q_t")),
            1) # dynamic type check on p
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : L q_t : p_t & q_t"))(True),
            1) # dynamic type check on (inner argument) q
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : p_t & q_t"), q=True)(False),
            False) # over-application
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : p_t & q_t"), q=True),
            False, False) # dynamic type check on p (bool vs tuple / missing _uncurry)
        self.assertRaises(TypeError,
            meta.exec(te("L p_t : L q_t : p_t & q_t"), _uncurry=True),
            False) # underapplication on uncurried function

    def test_set_simplify(self):
        for i in range(100):
            # XX random concrete sets to simplify/exec?
            x = random_expr(options=RType.SET_RELATION, depth=3)
            try:
                x.simplify_all(eliminate_sets=True, reduce=True)
            except:
                print(f"Simplify failure on depth 3 set expression '{repr(x)}'")
                raise

    def test_tuple(self):
        # a few basic type adjustment cases
        x = te('(a_n, b_e, c_X, d_<Y,Z>)')
        self.assertEqual(x.type, tp('(n,e,X,<Y,Z>)'))
        self.assertEqual(
            x.try_adjust_type(tp('(n,e,e,<e,t>)')).type,
            tp('(n,e,e,<e,t>)'))
        self.assertEqual(
            x.try_adjust_type(tp('(n,e,X,X)')).type,
            tp('(n,e,<Y,Z>,<Y,Z>)'))
        self.assertEqual(
            x.try_adjust_type(tp('(n,e,e,<X,X>)')).type,
            tp('(n,e,e,<e,e>)'))

        # the above tests, but in the context of using a tuple as a function
        # argument
        x = te('f_<∀X,t>(a_n, b_e, c_X, d_<Y,Z>)')
        self.assertEqual(
            te('f_<∀X,t>(a_n, b_e, c_X, d_<Y,Z>)')[0].type,
            tp('<(n,e,X,<Y,Z>),t>'))
        self.assertEqual(
            te('f_<(n,e,e,<e,t>),t>(a_n, b_e, c_X, d_<Y,Z>)')[0].type,
            tp('<(n,e,e,<e,t>),t>'))
        self.assertEqual(
            te('f_<(n,e,X,X),t>(a_n, b_e, c_X, d_<Y,Z>)')[0].type,
            tp('<(n,e,<Y,Z>,<Y,Z>),t>'))
        self.assertEqual(
            te('f_<(n,e,e,<X,X>),t>(a_n, b_e, c_X, d_<Y,Z>)')[0].type,
            tp('<(n,e,e,<e,e>),t>'))

        # tests for tuple indices
        testsimp(self, te('(_c1, 23)[0]'), '_c1', exec=True)
        testsimp(self, te('(_c1, 23)[1]'), 23, exec=True)

        # test the meta variant
        x = meta.MetaTerm(('_c1', 23))
        testsimp(self, core.TupleIndex(x, 0), '_c1', exec=True)
        testsimp(self, core.TupleIndex(x, 1), 23, exec=True)

        # basic index variable cases
        x = te('L x_n : (_c1, 23)[x]')
        self.assertEqual(x.type, tp('<n,[e|n]>'))
        # these are a bit weird, but they are the current behavior:
        self.assertEqual(x(0).type, tp('[e|n]'))
        self.assertEqual(x(1).type, tp('[e|n]'))
        self.assertEqual(x(2).type, tp('[e|n]')) # doesn't raise until reduction!
        testsimp(self, x(0), '_c1', exec=True, reduce=True)
        testsimp(self, x(1), 23, exec=True, reduce=True)
        self.assertRaises(meta.MetaIndexError, x(2).reduce_all)

        # test the meta version of this (not constructable in the metalanguage
        # parser, but should have identical behavior)
        x = meta.core.LFun(te('x_n'),
                    meta.core.TupleIndex(meta.MetaTerm(('_c1', 23)), te('x_n')))
        self.assertEqual(x.type, tp('<n,[e|n]>'))
        # these are a bit weird, but they are the current behavior:
        self.assertEqual(x(0).type, tp('[e|n]'))
        self.assertEqual(x(1).type, tp('[e|n]'))
        self.assertEqual(x(2).type, tp('[e|n]')) # doesn't raise until reduction!
        testsimp(self, x(0), '_c1', exec=True, reduce=True)
        testsimp(self, x(1), 23, exec=True, reduce=True)
        self.assertRaises(meta.MetaIndexError, x(2).reduce_all)

        # now test some type adjustment cases
        x = te('L x_n : (_c1, 23)[x]').try_adjust_type(tp('<n,e>'))
        self.assertEqual(x.type, tp('<n,e>'))
        self.assertEqual(x(0).type, tp('e'))
        self.assertEqual(x(1).type, tp('e')) # does not raise on application!
        # self.assertEqual(x(0).reduce_all(), te('a_e'))
        testsimp(self, x(0), te('_c1'), exec=True, reduce=True)
        self.assertRaises(meta.MetaIndexError, x(1).reduce_all)
        self.assertEqual(
            te('L x_n : (_c1, 23)[x]').try_adjust_type(tp('<n,t>')),
            None)

        x = te('L x_n : (_c1, b_Y)[x]').try_adjust_type(tp('<n,n>'))
        self.assertEqual(x.type, tp('<n,n>'))
        self.assertEqual(x(0).type, tp('n'))
        self.assertEqual(x(1).type, tp('n'))
        self.assertRaises(meta.MetaIndexError, x(0).simplify_all, reduce=True)
        testsimp(self, x(1), te('b_n'), all=True, reduce=True)

        # Weird case (see extensive comment in TupleIndex.resolve_type). The
        # type adjustment applies to both type variables. This behavior may
        # change in the future, but this tests the current contract.
        x = te('L x_n : (a_X, b_Y)[x]').try_adjust_type(tp('<n,n>'))
        self.assertEqual(x.type, tp('<n,n>'))
        self.assertEqual(x(0).type, tp('n'))
        self.assertEqual(x(1).type, tp('n'))
        testsimp(self, x(0), te('a_n'), all=True, reduce=True)
        testsimp(self, x(1), te('b_n'), all=True, reduce=True)

    def test_listedset(self):
        # these are not exhaustive, but relatively target to specific issues
        self.assertEqual(te("{y_X}").try_adjust_type(tp("{e}")).type, tp("{e}"))
        s = te("{x_Z, y_<e,Y>, z_<X,t>}", let=False)
        self.assertEqual(s.type, tp("{<e,t>}"))
        for e in s:
            self.assertEqual(e.type, tp("<e,t>"))

    def test_set_identities(self):
        t_set = te("Set x_e : True")
        cf_set = te("Set x_e : False")
        # reminder, te("{}") has a polymorphic type out of the gate
        lf_set = sets.emptyset(innertype=tp("e"))
        testsimp(self, cf_set, lf_set, all=True, exec=True)
        for f_set in [cf_set, lf_set]:
            # if the output is t_set, compilation is not possible
            testsimp(self, t_set & t_set, t_set, all=True)
            testsimp(self, t_set & f_set, lf_set, all=True, exec=True)
            testsimp(self, f_set & t_set, lf_set, all=True, exec=True)
            testsimp(self, f_set & f_set, lf_set, all=True, exec=True)

            testsimp(self, t_set | t_set, t_set, all=True)
            testsimp(self, t_set | f_set, t_set, all=True)
            testsimp(self, f_set | t_set, t_set, all=True)
            testsimp(self, f_set | f_set, lf_set, all=True, exec=True)

            testsimp(self, t_set - t_set, lf_set, all=True, exec=True)
            testsimp(self, t_set - f_set, t_set, all=True)
            testsimp(self, f_set - t_set, lf_set, all=True, exec=True)
            testsimp(self, f_set - f_set, lf_set, all=True, exec=True)

            testsimp(self, t_set.equivalent_to(t_set), True, all=True, exec=True)
            testsimp(self, t_set.equivalent_to(f_set), False, all=True, exec=True)
            testsimp(self, f_set.equivalent_to(t_set), False, all=True, exec=True)
            testsimp(self, f_set.equivalent_to(f_set), True, all=True, exec=True)


            # <=> in general has compilation issues with t_set. The basic cases
            # are all special cased, but all sorts of more general cases can't
            # be handled. Unfortunately this extends to many of the derived
            # relations that use <=>. Ideally all of these should work, but
            # at the moment I only see how to do this by adding yet more special
            # casing, which I don't want to do. Static simplification handles
            # all of these.
            testsimp(self, t_set <= t_set, True, all=True)
            testsimp(self, t_set <= f_set, False, all=True)
            testsimp(self, f_set <= t_set, True, all=True, exec=True)
            testsimp(self, f_set <= f_set, True, all=True, exec=True)
            testsimp(self, t_set < t_set, False, all=True)
            testsimp(self, t_set < f_set, False, all=True)
            testsimp(self, f_set < t_set, True, all=True, exec=True)
            testsimp(self, f_set < f_set, False, all=True, exec=True)

            # test a few more complicated cases. It could be good to do these
            # more systematically. Many of these have compilation issues when
            # t_set is embedded. This first case is a good example of this;
            # static simplify can render this executable.
            testsimp(self, (t_set & t_set) & f_set, lf_set, all=True)
            testsimp(self, (t_set & f_set) & t_set, lf_set, all=True, exec=True)
            testsimp(self, (f_set | t_set) | f_set, t_set, all=True)
            testsimp(self, (t_set - f_set) - f_set, t_set, all=True)
            testsimp(self, (t_set - f_set) - t_set, lf_set, all=True, exec=True)

    def test_model(self):
        # see model documentation; example based on a Chierchia & McConnell-Ginet
        # example
        m1 = meta.Model(
            {'Bond': '_c1',
             'Pavarotti': '_c2',
             'Loren': '_c3',
             'J': 'Bond',
             'M': 'Loren',
             'P': {'Loren', 'Pavarotti'},
             'Q': {'Loren', 'Bond'},
             'K': {('Bond', 'Bond'), ('Bond', 'Loren'), ('Loren', 'Pavarotti'), ('Pavarotti', 'Loren')},
             'G': {('Bond', 'Loren', 'Pavarotti'), ('Loren', 'Loren', 'Bond'),
                   ('Loren', 'Bond', 'Pavarotti'), ('Pavarotti', 'Pavarotti', 'Loren')}
            },
            domain={'_c1', '_c2', '_c3'})

        self.assertRaises(TypeMismatch, m1.evaluate, te("Bond_t"))
        self.assertRaises(meta.DomainError, m1.evaluate, te("_c4"))

        def mod_eq(m, expr, r):
            eval_x = m.evaluate(te(expr))
            self.assertEqual(eval_x, r)
            with m.under():
                x = te(expr).simplify_all() # reduce should not be required
                self.assertEqual(x, eval_x) # probably redundant
                self.assertEqual(x, r)
            self.assertEqual(x, eval_x)

        mod_eq(m1, "Bond_e", '_c1')
        mod_eq(m1, "P_<e,t>(Loren_e)", True)
        mod_eq(m1, "P_<e,t>(Bond_e)", False)
        mod_eq(m1, "P_<e,t>(M_e) & Q_<e,t>(Pavarotti_e)", False)
        mod_eq(m1, "G_<(e,e,e),t>(Bond_e, J_e, _c1)", False)
        mod_eq(m1, "G_<(e,e,e),t>(Bond_e, M_e, _c2)", True)
        mod_eq(m1, "~P_<e,t>(Bond_e) <=> K_<(e,e),t>(Loren_e,J_e)", False)
        mod_eq(m1, "~(Bond_e <=> J_e) >> ~G_<(e,e,e),t>(Bond_e,Bond_e,Bond_e)", True)
        mod_eq(m1, "Exists x1_e : P_<e,t>(x1)", True)
        mod_eq(m1, "Forall x1_e : Exists x2_e : K_<(e,e),t>(x1,x2)", True)
        mod_eq(m1, "Exists x2_e : Forall x1_e : K_<(e,e),t>(x1,x2)", False)

        g1 = meta.Assignment(
            x1=te('Bond_e'),
            x2=te('Loren_e'),
            x3=te('Pavarotti_e'))

        with m1.under() as m:
            # Check that types are set from model
            self.assertEqual(te("P(Loren)").simplify_all(), True)
            # check some cases with multiple scopes
            with m(g1).under():
                self.assertEqual(
                    te("G(x1, J, x1)").simplify_all(),
                    False)
                self.assertEqual(
                    te("~(G(x1,x1,x1) >> (J <=> M)) & (~Q(J) & K(J,M))").simplify_all(),
                    False)
                self.assertEqual(
                    te("~(x1 <=> J) >> ~G(x1,x1,x1)").simplify_all(),
                    True)

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
