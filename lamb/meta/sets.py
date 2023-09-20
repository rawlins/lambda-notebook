import random
import lamb
from lamb import types, utils
from .core import derived, registry, get_type_system, BindingOp, TypedExpr
from .core import BinaryGenericEqExpr, SyncatOpExpr, LFun, TypedTerm
from .boolean import BinaryOrExpr
from lamb.types import type_t, SetType

def setup_operators():
    # type {X}
    registry.add_operator(SetContains, None, None)
    registry.add_binding_op(ConditionSet)

class ConditionSet(BindingOp):
    """A set represented as a condition on a variable.

    The body must be of type t."""

    canonical_name = "Set"
    op_name_uni="Set"
    op_name_latex="Set"

    def __init__(self, var_or_vtype, body, varname=None, assignment=None,
                                                            type_check=True):
        body = self.ensure_typed_expr(body, assignment=assignment)
        super().__init__(var_or_vtype=var_or_vtype, typ=None, body=body,
                varname=varname, body_type=types.type_t, assignment=assignment,
                type_check=type_check)
        self.type = SetType(self.vartype)

    def structural_singleton(self):
        pass

    def term(self):
        return False

    def latex_str(self, parens=True, **kwargs):
        return utils.ensuremath("\\{%s_{%s}\\:|\\: "
                            % (self.varname, self.vartype.latex_str())
                    + self.body.latex_str(**kwargs) + "\\}")

    def __lshift__(self, i):
        return SetContains(i, self)

    def to_characteristic(self):
        """Return a LFun based on the condition used to describe the set."""
        return LFun(self.vartype, self.body, self.varname)

    def try_adjust_type_local(self, unified_type, derivation_reason,
                                                            assignment, env):
        inner_type = unified_type.content_type
        char = self.to_characteristic()
        sub_var = TypedTerm(self.varname, inner_type)
        new_condition = char.apply(sub_var)
        return self.copy_local(sub_var, new_condition)

class ListedSet(TypedExpr):
    """A listed set is a set that simply lists members."""
    canonical_name = "ListedSet"
    op_name_uni="ListedSet"
    op_name_latex="ListedSet"

    def __init__(self, iterable, typ=None, assignment=None, type_check=True):
        s = set(iterable) # remove duplicates, flatten order
        args = [self.ensure_typed_expr(a,assignment=assignment) for a in s]
        args = sorted(args, key=repr) # for a canonical ordering
        if len(args) == 0 and typ is None:
            typ = types.VariableType("X") # could be a set of anything
        elif typ is None:
            typ = args[0].type
        for i in range(len(args)):
            # type checking TODO: this isn't right, would need to pick the
            # strongest type
            args[i] = self.ensure_typed_expr(args[i], typ)
        super().__init__("Set", *args)
        #self.op = "Set"
        self.type = SetType(typ)

    def subst(self, i, s):
        if len(self.args) < 2:
            return super().subst(i, s)
        else:
            raise NotImplementedError(
                "Beta reduction into a set of size>1 not currently supported.")
            # TODO deal with this
            # the problem is the same as usual -- set order isn't stable so we
            # need to do this all at once rather than  member-by-member.

    def copy(self):
        return ListedSet(self.args)

    def copy_local(self, *args, type_check=True):
        return ListedSet(args)

    def term(self):
        return False

    def __lshift__(self, i):
        """Use the `<<` operator for set membership."""
        return SetContains(i, self)

    def set(self):
        """Return a python `set` version of the ListedSet.

        Note that this isn't guaranteed to be defined for everythingthing with a
        set type."""
        return set(self.args)

    def cardinality(self):
        return len(self.args)

    def to_condition_set(self):
        """Convert to a condition set by disjoining members."""
        # ensure that we build a condition set from a variable that is not free
        # in any of the members
        varname = self.find_safe_variable(starting="x")
        conditions = [BinaryGenericEqExpr(
                                            TypedTerm(varname, a.type), a)
                                                            for a in self.args]
        return ConditionSet(self.type.content_type,
                            BinaryOrExpr.join(*conditions),
                            varname=varname)

    def reduce_all(self):
        """Special-cased reduce_all for listed sets.  There are two problems.
        First, the reduction may actually result in a change in the size of the
        set, something generally not true of reduction elsewhere.  Second,
        because the constructor calls `set`, `copy` is not guaranteed to return
        an object with a stable order.  Therefore we must batch the reductions
        (where the TypedExpr version doesn't).

        Note that currently this produces non-ideal derivation sequences."""
        dirty = False
        accum = list()
        result = self
        for i in range(len(result.args)):
            new_arg_i = result.args[i].reduce_all()
            if new_arg_i is not result.args[i]:
                dirty = True
                reason = "Recursive reduction of set member %s" % (i+1)
                # TODO: this isn't quite right but I can't see what else to do
                # right now
                result = derived(result, result, desc=reason,
                                    subexpression=new_arg_i, allow_trivial=True)
                accum.append(new_arg_i)
            else:
                accum.append(new_arg_i)
        if dirty:
            new_result = ListedSet(accum)
            new_result = derived(new_result, result,
                            desc="Construction of set from reduced set members")
            result = new_result
        return result


    def __repr__(self):
        return repr(set(self.args))

    def latex_str(self, **kwargs):
        inner = ", ".join([a.latex_str(**kwargs) for a in self.args])
        return utils.ensuremath("\\{" + inner + "\\}")

    def try_adjust_type_local(self, unified_type, derivation_reason, assignment,
                                                                        env):
        inner_type = unified_type.content_type
        content = [a.try_adjust_type(inner_type,
                        derivation_reason=derivation_reason,
                        assignment=assignment) for a in self.args]
        result = self.copy_local(*content)
        return result

    @classmethod
    def random(self, ctrl, max_type_depth=1, max_members=6, allow_empty=True):
        typ = get_type_system().random_type(max_type_depth, 0.5)
        if allow_empty:
            r = range(max_members+1)
        else:
            r = range(max_members+1)[1:]
        length = random.choice(r)
        members = [ctrl(typ=typ) for i in range(length)]
        return ListedSet(members)


class SetContains(SyncatOpExpr):
    """Binary relation of set membership.  This uses `<<` as the symbol.

    Note that this _does_ support reduction if the set describes its members by
    condition, as set membership is equivalent to saturation of the
    characteristic function of the set."""

    arity = 2
    canonical_name = "<<"
    # ∈ should work but I was having trouble with it (long ago, recheck)
    op_name_latex = "\\in{}"

    def __init__(self, arg1, arg2, type_check=True):
        # seems like the best way to do the mutual type checking here?
        # Something more elegant?
        arg1 = self.ensure_typed_expr(arg1)
        arg2 = self.ensure_typed_expr(arg2, SetType(arg1.type))
        arg1 = self.ensure_typed_expr(arg1, arg2.type.content_type)
        super().__init__(type_t, arg1, arg2, tcheck_args=False)

    def copy(self):
        return SetContains(self.args[0], self.args[1])

    def copy_local(self, arg1, arg2, type_check=True):
        return SetContains(arg1, arg2)

    def reduce(self):
        if isinstance(self.args[1], ConditionSet):
            derivation = self.derivation
            step = (self.args[1].to_characteristic()(self.args[0])).reduce()
            step.derivation = derivation # suppress the intermediate parts of
                                         # this derivation, if any
            return derived(step, self, "∈ reduction")
        else:
            # leave ListedSets as-is for now.  TODO could expand this using
            # disjunction.
            return self

    def reducible(self):
        if isinstance(self.args[1], ConditionSet):
            return True
        return False

    @classmethod
    def random(cls, ctrl, max_type_depth=1):
        content_type = get_type_system().random_type(max_type_depth, 0.5)
        return SetContains(ctrl(typ=content_type), ctrl(
                                            typ=SetType(content_type)))

