import lamb.types, lamb.parsing, lamb.utils
from . import core, meta, ply
from .core import get_type_system, tp, SyncatOpExpr
from lamb.utils import ensuremath
from lamb.types import is_type, demeta, TupleType, type_t
from .ply import derived


def setup_operators(language):
    language.type_system.add_nonatomic(TypeType)
    language.registry.add_operator(TypeOp)
    language.registry.add_operator(TypeEquivalence)


class TypeDomainSet(lamb.types.ComplexDomainSet):
    def __init__(self, typ=None, symbol="type"):
        super().__init__(symbol, typ=typ)
        self._finite = False

    def check(self, x):
        return is_type(x)

    def __repr__(self):
        return "type"

    def __iter__(self):
        # for now, just prevent iteration...leads to too many issues.
        raise ValueError("Can't iterate over `TypeDomainSet`.")

    @classmethod
    def element_to_type(cls, x, ctrl=None):
        if is_type(x):
            return TypeType()
        return None

    def element_repr(self, x, rich=False, **kwargs):
        x = demeta(x)
        if rich:
            # currently, it's not possible to actually *use* a
            # type's rich repr. (Main consequence: unaesthetic <>)
            return f"{repr(x)}"
        else:
            return f"type {repr(x)}"


class TypeType(lamb.types.TypeConstructor):
    domain_class = TypeDomainSet

    def __init__(self):
        super().__init__(symbol="Type")

    def __repr__(self):
        return "Type"

    def latex_str(self, **kwargs):
        return ensuremath("\\text{Type}")

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        m, new_i = lamb.parsing.consume_pattern(s, i, 'Type')
        if m is None:
            return (None, i)
        else:
            return (TypeType(), new_i)

    @classmethod
    def random(cls, random_ctrl_fun):
        return TypeType()


class TypeOp(core.SyncatOpExpr):
    arity = 1
    canonical_name = "Type"
    operator_style = False
    arg_signature = tp("(X,)")
    
    def __init__(self, arg, typ=None, **kwargs):
        if typ is None:
            typ = TypeType()
        typ = self.type_constraint(typ, TypeType)
        super().__init__(None, arg, typ=typ, tcheck_args=False)

    def _compile(self):
        # TODO: cannot handle cases where a polymorphic variable receives a
        # non-polymorphic value during execution. For example:
        #   x = %te Type(x_X)
        #   lamb.meta.exec(x, x='_c1')
        # (as long as these are embedded in a <=> expression, there will be an error at least)

        arg = self[0]._compiled # ensure that this gets compiled, even if it is ignored
        return self.simplify()._compiled

    def simplify(self, **sopts):
        return derived(meta.MetaTerm(self[0].type), self, "Type evaluation")


# need to provide a specialized equivalence operation in order to handle
# comparison with polymorphic types. Under this notion of equivalence, only
# concrete types can be compared to, so polymorphic type comparison is deferred
# without a value for type variables. (Without something like this, the
# Church-Rosser property is violated.)
class TypeEquivalence(SyncatOpExpr):
    """Binary relation of type equivalence, simplifying only for non-polymorphic types."""

    canonical_name = "<=>"
    secondary_names = {"==", "%"}
    op_name_latex = "="
    commutative = True

    # can't use tp, since Type is only added by setup
    # arg_signature = tp("(Type,Type)")
    arg_signature = TupleType(TypeType(), TypeType())

    def __init__(self, arg1, arg2, typ=None, **kwargs):
        typ = self.type_constraint(typ, type_t, constant=True)
        # Could even generalize this to handle args of completely arbitrary
        # types
        super().__init__(TypeType(), arg1, arg2, typ=typ)

    def _compile(self):
        a1 = self[0]._compiled
        a2 = self[1]._compiled
        def impl(context):
            t1 = a1(context)
            t2 = a2(context)
            # the following error prevents comparison in cases like the following,
            # which currently can't be handled well:
            #   x = %te Type(x_X) <=> type e
            #   lamb.meta.exec(x, x='_c1')
            if t1.is_polymorphic() or t2.is_polymorphic():
                raise TypeError(f"Unable to statically evaluate polymorphic type for `{self}`")
            return t1 == t2
        return impl

    def simplify(self, **sopts):
        # a more sophisticated (i.e. better) approach might simplify polymorphic
        # types in let-bound contexts as long as they are locally free, by
        # using unification
        if (self[0].meta() and self[1].meta()
                and not self[0].op.is_polymorphic()
                and not self[1].op.is_polymorphic()):
            return derived(meta.MetaTerm(self[0].op == self[1].op), self, "Type equivalence")
        else:
            return self
