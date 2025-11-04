import lamb.types, lamb.parsing, lamb.utils
from . import core, meta, ply
from .core import get_type_system, tp
from lamb.utils import ensuremath
from lamb.types import is_type, demeta
from .ply import derived


def setup_operators(language):
    language.type_system.add_nonatomic(TypeType)
    language.registry.add_operator(TypeOp)


class TypeDomainSet(lamb.types.ComplexDomainSet):
    def __init__(self, typ=None, symbol="type"):
        super().__init__(symbol, typ=typ)
        self._finite = False

    def check(self, x):
        return is_type(x)

    def __repr__(self):
        return "type"

    def __iter__(self):
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


def try_parse_type_term(s, i):
    m, next = lamb.parsing.consume_pattern(s, i, 'type ')
    if m is None:
        raise lamb.parsing.ParseError("Failed to match `type `",
            s=s, i=i, met_preconditions=False)
    typ, end = lamb.meta.parser.type_parser.parse(s, next) # should raise
    assert(typ is not None)
    return typ, end


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

    def simplify(self, **sopts):
        return derived(meta.MetaTerm(self[0].type), self, "Type evaluation")
