#!/usr/local/bin/python3
# -*- coding: utf-8 -*-
import sys, re, random, collections.abc, math, functools, itertools, contextlib
from numbers import Number
from contextlib import contextmanager
import logging

from lamb import utils, parsing
from lamb.utils import *

# constant for third truth value
global Maybe, random_len_cap
Maybe = 2

random_len_cap = 5


def demeta(x):
    # the import here needs to be very narrow, to avoid circular import issues
    from lamb.meta.meta import MetaTerm
    if isinstance(x, MetaTerm):
        return x.op
    else:
        return x


def curlybraces(x, rich=False):
    if rich:
        # assume `rich` == embedded in latex
        return f"\\{{{x}\\}}"
    else:
        return f"{{{x}}}"


# in principle, one might want to inherit from abc.collections.Set. However,
# because this can represent an infinite set, sometimes the collection has
# no length, which is required for most stronger types in collections.abc.
class DomainSet(collections.abc.Container):
    type = None # class variable
    def __init__(self, finite=True, values=None, typ=None, superdomain=None):
        self.finite = finite
        self.superdomain = superdomain
        if values is None:
            values = set()
        self.domain = set(values)
        if typ is not None:
            # override class value at the instance level
            self.type = typ

    def __repr__(self):
        if not self.finite:
            return "Anonymous non-finite domain" # should not be reachable...
        if self.superdomain is not None:
            # this is not a proper repr...
            return f"Subdomain {repr(self.domain)} of {repr(self.superdomain)}"
        return f"DomainSet({repr(self.domain)})"

    def normalize(self, x):
        if self.superdomain is not None:
            return self.superdomain.normalize(x)
        return x

    def check(self,x):
        if self.finite:
            try:
                return (demeta(self.normalize(x)) in self.domain)
            except TypeError:
                # this is a bit broad, but the aim is catch non-hashable
                # objects
                return False
        else:
            return self.infcheck(demeta(self.normalize(x)))

    def __contains__(self, x):
        return self.check(x)

    def __len__(self):
        # can't do something like return math.inf for this case, because it's
        # not an int:
        # https://docs.python.org/3/reference/datamodel.html#object.__len__
        if not self.finite:
            raise ValueError("Non-finite `DomainSet`s do not have a length.")
        return len(self.domain)

    def cardinality(self):
        if self.finite:
            return len(self)
        else:
            # no support for different infinite cardinalities, but in practice,
            # this basically means countably infinite.
            return math.inf

    def __iter__(self):
        if self.finite:
            return iter(self.domain)
        else:
            raise NotImplementedError(
                "Can't iterate over an abstract infinite set")

    def enumerable(self):
        # by default, conflate enumerability with finiteness
        return self.finite

    def infcheck(self, x):
        """Does `x` meet the criteria for being a member of a set if infinite?"""
        raise NotImplementedError(
            "Can't check membership for an abstract infinite set")

    def element_rename(self, x):
        if self.type is not None and x in self.type.domain_names:
            return self.type.domain_names[x]
        else:
            return None

    def element_repr(self, x, rich=False, use_renames=True, **kwargs):
        if use_renames and (rename := self.element_rename(x)):
            x = rename
        x = demeta(x)
        if not isinstance(x, str):
            x = repr(x)

        if rich and x.startswith("_"):
            x = x[1:]
        return x

    def random(self):
        if self.finite:
            # XX this may not be seed stable if the list is constructed every time
            return random.choice(list(self.domain))
        else:
            raise NotImplementedError("Can't pick randomly from an abstract infinite set")

    @classmethod
    def element_to_type(cls, x, ctrl=None):
        # this can be used for singleton classes, as long as they have `type`
        # set.
        if cls.type is not None and cls.type.domain.check(x):
            return cls.type
        else:
            return None


class BooleanSet(DomainSet):
    def __init__(self):
        # to prevent circularity, BooleanSet.type is set in reset()
        super().__init__(finite=True, values=[False,True])

    def check(self,x):
        # bool is implemented as a subclass of int, and therefore 0 and 1 are
        # equivalent (both hashing, and via ==) to False and True. Checking
        # for set membership in {False,True} includes 0/1 in the domain.
        # This perhaps could be useful if we have a way of normalizing the
        # term names, but for now, instead of using the superclass `in`
        # check, exclude 0/1 from the domain by checking class directly.
        return isinstance(demeta(x), bool)

    def modify_domain(self, values=None, count=None):
        # allowing this messes up too many things, and I don't think there's
        # much of a use case for it
        raise ValueError("Domain restriction for type t is not supported")

    @contextlib.contextmanager
    def restrict_domain(self, values=None, count=None):
        raise ValueError("Domain restriction for type t is not supported")

    def normalize(self, x):
        return bool(x)

    def __repr__(self):
        return f"BooleanSet()"


class SimpleInfiniteSet(DomainSet):
    """Arbitrary domain type modeling a (countable) non-finite set. Elements are
    strings consisting of a prefix followed by a natural number."""
    def __init__(self, prefix, typ=None):
        super().__init__(finite=False, typ=typ)
        self.prefix = prefix
        # this disallows sequences like 001; an alternative would be to
        # normalize them...
        # in principle, the _ could be ignored here due to normalization
        self.symbol_re = re.compile(fr'_?({prefix}(?:0|[1-9][0-9]*))$')
        # TODO better error checking

    def infcheck(self, x):
        return isinstance(x, str) and re.match(self.symbol_re, x)

    def normalize(self, x):
        if isinstance(x, str) and not x.startswith("_"):
            return "_" + x
        return x

    def __iter__(self):
        i = 0
        while True:
            # we use the `_` for convenience, to ensure that the strings
            # will instantiate correctly via `te`
            yield f"_{self.prefix}{i}"
            i += 1

    def enumerable(self):
        return True

    def random(self, limit=None):
        if limit is None:
            # python 3 has no maxint, this is semi-arbitrary
            limit = 2 ** 16 - 1
        return f"_{self.prefix}{random.randint(0,limit)}"

    def __repr__(self):
        return f"SimpleInfiniteSet('{self.prefix}')"

    @classmethod
    def element_to_type(cls, x, ctrl):
        # should be handled by the type system
        raise NotImplementedError(
            "Can't check membership for abstract infinite domain set")


def is_numeric(x):
    # bools are Number instances, exclude them here
    return isinstance(x, Number) and not isinstance(x, bool)


# TODO: this class is quite hedgy about what specific numbers we're talking
# about...maybe should fix on ints?
# * iterator and random are ints only
# * parser does not accept floats
# * MetaTerm constructor will take floats
# * infcheck is any numeric (non-bool)
# * no handling for aleph 0 vs 1...
class SimpleNumericSet(DomainSet):
    """Class backed by python `Number`s"""
    def __init__(self):
        # to prevent circularity, SimpleNumericSet.type is set in reset()
        super().__init__(finite=False)

    def infcheck(self, x):
        return is_numeric(x)

    def __iter__(self):
        # iterate over ints only....
        i = 0
        yield i
        while True:
            i += 1
            yield i
            yield -i

    def enumerable(self):
        return True

    def random(self, limit=None):
        # this will only return ints...is that a problem?
        if limit is None:
            # python 3 has no maxint, this is semi-arbitrary
            limit = 2 ** 16 - 1
        return random.randint(-limit,limit)

    def __repr__(self):
        return f"SimpleNumericSet()"


def is_type(x):
    return isinstance(x, TypeConstructor)


# domain set handling for complex types, e,g, <(e,e),t> etc. that can't be
# pre-constructed (there is a non-finite set of these).
class ComplexDomainSet(SimpleInfiniteSet):
    def __init__(self, prefix, typ, finite=False):
        super().__init__(prefix, typ=typ)
        self.finite = finite

    def __iter__(self):
        raise NotImplementedError(
            "Can't iterate over a complex domain set")

    def infcheck(self, x):
        """Does `x` meet the criteria for being a member of a set if infinite?"""
        raise NotImplementedError(
            "Can't check membership for an abstract complex domain set")

    def check(self,x):
        # don't use regular membership checking even for finite sets of this class
        return self.infcheck(demeta(x))

    def enumerable(self):
        return False

    def element_repr(self, x, rich=False, **kwargs):
        preprefix = (not rich) and "_" or ""
        return f"{preprefix}{self.prefix}[anon]"

    @classmethod
    def element_to_type(cls, x, ctrl=None):
        raise NotImplementedError(
            "Can't check membership for abstract complex domain sets")


# this wrapper class is currently trivial. It could be removed, but it may be
# useful if smarter cache handling of variable types were to ever return
class CachableType:
    def __init__(self, t):
        self.t = t

    def __eq__(self, other):
        return self.t._type_eq(other.t)

    def __hash__(self):
        return self.t._type_hash()

    def __repr__(self):
        return repr(self.t)


try:
    from itertools import batched # py3.12 only
except:
    # back compat placeholder, XX hopefully this is robust enough
    def batched(iterable, size):
        sourceiter = iter(iterable)
        while True:
            batchiter = itertools.islice(sourceiter, size)
            # the following will raise StopIteration when needed
            yield itertools.chain([next(batchiter)], batchiter)


class TypeConstructor(object):
    domain_class = None
    def __init__(self, domain=None):
        self.symbol = None
        self.unify_source = None
        self.generic = False
        self.init_type_vars()
        if domain is None:
            if self.domain_class is None:
                domain = set()
            else:
                domain = self.domain_class(typ=self)
        self.domain = domain
        self.domain_names = {}

    def __eq__(self, other):
        return self._type_eq(other)

    def __hash__(self):
        return self._type_hash()

    def _type_eq(self, other):
        # in principle, could use the sequence interface to implement this
        # more generically
        raise NotImplementedError

    def _type_hash(self):
        raise NotImplementedError

    def __len__(self):
        return 0

    def __getitem__(self, i):
        raise IndexError

    def __iter__(self):
        return iter(list())

    def functional(self):
        raise NotImplementedError

    def check(self, x):
        raise NotImplementedError

    def get_subdomain(self, values=None, count=None):
        """Get a DomainSet object that is a (finite) subdomain of this type's
        domain. The subdomain can be chosen by value, or (as long as it is
        enumerable) by count. The latter will pick the first `count` elements
        of the current domain. The subdomain must be non-empty, and all
        elements if supplied by value must be in the current domain; the
        restriction can be trivial. Subdomains are not generally supported
        for complex types.

        This function does not change the type's domain itself. See also
        `restrict_domain` for a context manager interface to this function.
        """
        if count:
            if not self.domain.enumerable():
                raise ValueError(f"Can't get subdomain by count for non-enumerable domain of type {repr(self)}")
            if self.domain.cardinality() < count:
                raise ValueError(f"Domain for type {repr(self)} is too small to get {count} elements")
            values = set(next(batched(self.domain, count)))
        if self.domain.finite:
            if not self.domain.domain:
                # finite type that is not implemented via an explicit set,
                # perhaps something like <t,t> etc. This could be implemented
                # in principle...
                raise ValueError(f"Domain for type {repr(self)} does not support restriction")
            if not values <= self.domain.domain:
                raise ValueError(f"{repr(values)} is not a subset of domain for type {repr(self)}")
        else:
            if not all(x in self.domain for x in values):
                raise ValueError(f"{repr(values)} is not a subset of domain for type {repr(self)}")
        values = {demeta(self.domain.normalize(x)) for x in values}
        return DomainSet(values=values, typ=self, superdomain=self.domain)

    def modify_domain(self, values=None, count=None):
        if not isinstance(self.domain, DomainSet):
            raise ValueError(f"Can't modify domain for type {self}")
        if values and isinstance(values, DomainSet):
            # XX this doesn't validate the domain set against self!
            self.domain = values
        else:
            self.domain = self.get_subdomain(values=values, count=count)

    @contextlib.contextmanager
    def restrict_domain(self, values=None, count=None):
        saved = self.domain
        self.modify_domain(values=values, count=count)
        try:
            yield self.domain
        finally:
            self.domain = saved

    def reset_domain(self):
        if not isinstance(self.domain, DomainSet):
            return
        while self.domain.superdomain is not None:
            self.domain = self.domain.superdomain

    def set_name(self, name, elem, force=False):
        # XX should this be implemented on BasicType only?
        # XX what happens if assignments here go "out of scope" wrt domain
        # restrictions?
        if name is None:
            if elem in self.domain_names:
                del self.domain_names[elem]
        else:
            if not self.check(elem):
                raise ValueError(
                    f"Unknown domain element for type `{repr(self)}`: `{repr(elem)}`")
            if force or elem not in self.domain_names:
                self.domain_names[elem] = name

    def get_name(self, elem):
        return self.domain_names.get(elem, None)

    @contextlib.contextmanager
    def with_names(self, a, force=False):
        old = self.domain_names.copy()
        if force:
            i = reversed(a)
        else:
            i = a
        try:
            for k in i:
                self.set_name(k, a[k], force=force)
            yield
        finally:
            self.domain_names = old

    def copy_local(self, *parts):
        """Return a copy of the type with any local properties preserved,
        but *parts substituted appropriately.

        Note that for complex types, this acts much like a factory function."""
        raise NotImplementedError

    def copy(self):
        return self.copy_local(*list(iter(self)))

    def __repr__(self):
        raise NotImplementedError

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        raise NotImplementedError

    @classmethod
    def random(cls, random_ctrl_fun):
        print(repr(cls))
        raise NotImplementedError

    def bound_type_vars(self):
        """Returns all bound type variables in the type.  Reminder: In
        Damas-Hindley-Milner, the way it is normally used, all type variables
        are bound. So in practice, this gives all type variables."""
        return self._type_vars

    def is_let_polymorphic(self):
        return self._sublet

    def is_polymorphic(self):
        # doesn't count disjunctive types
        return len(self.bound_type_vars()) > 0 or self.is_let_polymorphic()

    def has_fresh_variables(self):
        return any(v.is_fresh() for v in self._type_vars)

    def init_type_vars(self):
        accum = set()
        self._sublet = False
        for part in iter(self):
            accum.update(part._type_vars)
            self._sublet = self._sublet or part._sublet
        self._type_vars = accum

    def sub_type_vars(self, assignment, trans_closure=False):
        """Substitute type variables in `self` given the mapping in
        `assignment`.

        This does only one-place substitutions, so it won't follow chains if
        there are any."""
        if len(self.bound_type_vars()) == 0:
            return self
        l = list()
        dirty = False
        for i in range(len(self)):
            l.append(self[i].sub_type_vars(assignment,
                                                trans_closure=trans_closure))
            if l[i] is not self[i]:
                dirty = True
        if dirty:
            return self.copy_local(*l)
        else:
            return self

    def unify(self, other, unify_control_fun, assignment=None):
        """General function for type unification.  Not intended to be called
        directly.  See `TypeSystem.unify`."""
        if not isinstance(self, other.__class__):
            return (None, assignment)
        if len(self) != len(other):
            return (None, assignment)
        sig = list()
        for i in range(len(self)):
            (part_result, assignment) = unify_control_fun(self[i], other[i], assignment=assignment)
            if part_result is None:
                return (None, assignment)
            sig.append(part_result)
        return (self.copy_local(*sig), assignment)


class BasicType(TypeConstructor):
    """Class for atomic types.  The core atomic type interface:

    symbol: the name of the type.
    functional(): must return False.

    Extras:
    values: an object implementing the DomainSet interface representing the set
    that this type characterizes.
    """

    # some convenient defaults for domain type prefixes, these can be
    # overridden.
    default_prefixes = {
        's': 'w',
        'e': 'c',
        'v': 'e'
        }

    def __init__(self, symbol, values=None, name=None):
        super().__init__()
        self.symbol = symbol
        if name is None:
            self.name = symbol
        else:
            self.name = name
        if values is None:
            # by default: use an infinite domain set backed by strings
            domain_symbol = self.default_prefixes.get(symbol, symbol)
            self.domain = SimpleInfiniteSet(domain_symbol, typ=self)
        else:
            self.domain = values
            if isinstance(self.domain, SimpleInfiniteSet):
                self.domain.type = self
        # pre-escape because of the use of "?" for undetermined type
        self.regex = re.compile(re.escape(self.symbol))

    def functional(self):
        return False

    def check(self, x):
        return self.domain.check(x)

    def copy_local(self):
        return BasicType(self.symbol, self.domain, self.name)

    def _type_eq(self, other):
        if isinstance(other, BasicType):
            return self.symbol == other.symbol
        else:
            return False

    def _type_hash(self):
        return hash(self.symbol)

    def __repr__(self):
        return "%s" % self.symbol

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self, **kwargs):
        return ensuremath(repr(self))

    def _repr_latex_(self):
        return self.latex_str()

    def add_internal_argument(self, arg_type):
        return FunType(arg_type, self)

    def unify(self, other, unify_control_fun, assignment=None):
        if self == other:
            return (self, assignment)
        else:
            return (None, assignment)


class FunDomainSet(ComplexDomainSet):
    def __init__(self, typ):
        finite = (isinstance(typ.left.domain, DomainSet) and typ.left.domain.finite
                    and isinstance(typ.right.domain, DomainSet) and typ.right.domain.finite)
        super().__init__("Fun", typ, finite=finite)

    def infcheck(self, x):
        # XX variable types
        if callable(x):
            # warning -- no further type checking for this case...
            # XX this would be pretty unsafe if it is user facing in any very
            # direct way. The purpose is so that compiled domain checks are
            # sufficiently general.
            return True
        elif self.type.right == type_t and isinstance(x, collections.abc.Set):
            # special case shorthand: when we are dealing with a characteristic
            # function, allow a set to be used.
            # XX this is very convenient, but does mean that python sets are
            # treated as multi-typed...
            return all(e in self.type.left.domain for e in x)
        elif isinstance(x, collections.abc.Mapping):
            if not all(e in self.type.left.domain for e in x):
                return False
            return all(x[k] in self.type.right.domain for k in x)
        else:
            return False

    def normalize(self, x):
        if callable(x):
            return x
        elif isinstance(x, collections.abc.Set):
            return frozenset(x)
        else: # mapping
            return utils.frozendict({
                self.type.left.domain.normalize(k): self.type.right.domain.normalize(x[k])
                for k in x})

    def __len__(self):
        if not self.finite:
            raise ValueError("Non-finite `FunDomainSet`s do not have a length.")
        else:
            return len(self.type.right.domain) ** len(self.type.left.domain)

    def __iter__(self):
        if not self.finite:
            raise ValueError("Can't iterate over non-finite `FunDomainSet`s.")
        # careful with this -- it can definitely blow up!
        dom = list(self.type.left.domain)
        for p in itertools.product(self.type.right.domain, repeat=len(dom)):
            yield utils.frozendict(list(zip(dom, p)))

    def enumerable(self):
        # only the finite case is supported right now...
        return self.finite

    def __repr__(self):
        return f"FunDomainSet({self.type})"

    def element_repr(self, x, rich=False, **kwargs):
        if isinstance(x, collections.abc.Set):
            return f"Fun[{SetType(self.type.left).domain.element_repr(x, rich=rich, **kwargs)}]"
        elif isinstance(x, collections.abc.Mapping):
            pairs = [(self.type.left.domain.element_repr(k, rich=rich, **kwargs),
                      self.type.right.domain.element_repr(x[k], rich=rich, **kwargs)) for k in x]
            if rich:
                mapping = curlybraces(",".join(f"{pair[0]}:{pair[1]}" for pair in pairs), rich=rich)
                return f"Fun[{mapping}]"
            else:
                # use a python-style `{key: val}` notation for string reprs.
                return curlybraces(", ".join(f"{pair[0]}: {pair[1]}" for pair in pairs), rich=rich)
        else:
            # not currently used
            return super().element_repr(x, rich=rich, **kwargs)

    @classmethod
    def element_to_type(cls, x, ctrl):
        if isinstance(x, collections.abc.Mapping):
            # at this point we should have a coherent mapping describing a
            # function, so any failures on recursion should raise
            left = [ctrl(k) for k in x]
            if len(left):
                for i in range(len(left)):
                    if left[i] is None:
                        # assumption: stable key order
                        bad_elem = [k for k in x][i]
                        raise parsing.ParseError(f"Unknown type domain element in function domain: `{repr(bad_elem)}`")
                if not left.count(left[0]) == len(left):
                    for t in left[1:]:
                        if t != left[0]:
                            raise TypeMismatch(left[0], t,
                                error=f"Inconsistent domain types in function domain: `{repr(x)}`")
            right = [ctrl(x[k]) for k in x]
            if len(right):
                for i in range(len(right)):
                    if right[i] is None:
                        # assumption: stable key order
                        bad_elem = [x[k] for k in x][i]
                        raise parsing.ParseError(f"Unknown type domain element in function range: `{repr(bad_elem)}`")
                if not right.count(right[0]) == len(right):
                    for t in right[1:]:
                        if t != right[0]:
                            raise TypeMismatch(right[0], t,
                                error=f"Inconsistent domain types in function range: `{repr(x)}`")
            # note: a python dict allows writing {} notation dicts with duplicate
            # keys, but later values overwrite earlier ones. There's no way to
            # "type check" this, which may be a bit unexpected from a
            # mathematical perspective.
            return FunType(left[0], right[0])
        # currently: does not act on sets
        return None


class FunType(TypeConstructor):
    """Class for non-atomic (functional) binary types.  These characterize a
    set of functions. The core functional type interface:

    functional(): must return True.
    left: the input/left type of functions in the set.
    right: the output/right type of functions in the set.
    """
    domain_class = FunDomainSet
    def __init__(self, left, right):
        self.left = left
        self.right = right
        TypeConstructor.__init__(self)

    def __len__(self):
        return 2

    def __getitem__(self, i):
        return (self.left, self.right)[i]

    def __iter__(self):
        return iter((self.left, self.right))

    def functional(self):
        return True

    def copy_local(self, l, r):
        return FunType(l, r)

    def check(self, x):
        raise NotImplementedError()

    def __repr__(self):
        return "<%s,%s>" % (self.left, self.right)

    def _type_eq(self, other):
        if isinstance(other, FunType):
            return (self.left._type_eq(other.left)
                and self.right._type_eq(other.right))
        else:
            return False

    def _type_hash(self):
        return (self.left._type_hash()
                ^ self.right._type_hash())

    def __call__(self, other):
        return FunType(self, other)

    def latex_str(self, **kwargs):
        return ensuremath("\\left\\langle{}%s,%s\\right\\rangle{}"
                            % (self.left.latex_str(), self.right.latex_str()))

    def _repr_latex_(self):
        return self.latex_str()

    def add_internal_argument(self, arg_type):
        return FunType(self.left, self.right.add_internal_argument(arg_type))

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "<")
        if next is None:
            return (None, i)
        else:
            i = next
            (left, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, ",", "Missing comma in type")
            (right, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, ">", "Unmatched < in function type")
            return (FunType(left, right), i)

    @classmethod
    def random(cls, random_ctrl_fun):
        return FunType(random_ctrl_fun(), random_ctrl_fun())


class SetDomainSet(ComplexDomainSet):
    def __init__(self, typ):
        finite = isinstance(typ.content_type.domain, DomainSet) and typ.content_type.domain.finite
        super().__init__("Set", typ, finite=finite)

    def infcheck(self, x):
        if isinstance(x, collections.abc.Set):
            return all(e in self.type[0].domain for e in x)
        else:
            return False

    def __iter__(self):
        if not self.finite:
            raise ValueError("Can't iterate over non-finite `SetDomainSet`s.")
        # careful with this -- it can definitely blow up!
        dom = list(self.type.content_type.domain)
        for r in range(len(dom) + 1):
            for e in itertools.combinations(dom, r):
                yield frozenset(e)

    def __len__(self):
        if not self.finite:
            raise ValueError("Non-finite `SetDomainSet`s do not have a length.")
        else:
            return 2 ** len(self.type[0].domain)

    def enumerable(self):
        # only the finite case is supported right now...
        return self.finite

    def normalize(self, x):
        return frozenset({self.type.content_type.domain.normalize(e) for e in x})

    def __repr__(self):
        return f"SetDomainSet({self.type})"

    def element_repr(self, x, rich=False, **kwargs):
        elements = list(x)
        return curlybraces(
            f"{','.join(self.type[0].domain.element_repr(elements[i], rich=rich) for i in range(len(elements)))}",
            rich=rich)

    @classmethod
    def element_to_type(cls, x, ctrl):
        if isinstance(x, collections.abc.Set):
            list_x = list(x)
            types = [ctrl(k) for k in list_x]
            if len(types):
                # at this point, we are trying to construct a set, so raise
                # on recursive failures
                for i in range(len(types)):
                    if types[i] is None:
                        raise parsing.ParseError(f"Unknown type domain element in set: `{repr(list_x[i])}`")
                if not types.count(types[0]) == len(types):
                    for t in types[1:]:
                        if t != types[0]:
                            raise TypeMismatch(types[0], t,
                                error=f"Inconsistent domain types in set: `{repr(x)}`")
                return SetType(types[0])
            else:
                # The empty set needs a concrete (non-variable) type here. This
                # is somewhat awkward (since in some cases it's not possible
                # to give it a type annotation very easily), but since we can't
                # infer the intended type, error out here.
                # (weirdly, parsing currently doesn't error if `{?}` is explicitly
                # provided...)
                raise parsing.ParseError(f"Can't infer a domain for the empty set: provide an explicit type")
        return None


class SetType(TypeConstructor):
    domain_class = SetDomainSet
    """Type for sets.  See `lang.ConditionSet` and `lang.ListedSet`."""
    def __init__(self, ctype):
        self.content_type = ctype
        super().__init__()

    def __len__(self):
        return 1

    def __getitem__(self, i):
        return (self.content_type,)[i]

    def __iter__(self):
        return iter((self.content_type,))

    def copy_local(self, ctype):
        return SetType(ctype)

    def functional(self):
        return False

    def check(self, x):
        raise NotImplementedError()

    def __repr__(self):
        return "{%s}" % repr(self.content_type)

    def latex_str(self, **kwargs):
        return ensuremath("\\left\\{%s\\right\\}"
                                            % self.content_type.latex_str())

    def _type_eq(self, other):
        if isinstance(other, SetType):
            return self.content_type._type_eq(other.content_type)
        else:
            return False

    def _type_hash(self):
        return hash("Set") ^ self.content_type._type_hash()

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "{")
        if next is None:
            return (None, i)
        else:
            i = next
            (ctype, i) = parse_control_fun(s, i)
            i = parsing.consume_char(s, i, "}", "Unmatched { in set type")
            return (SetType(ctype), i)

    @classmethod
    def random(cls, random_ctrl_fun):
        return SetType(random_ctrl_fun())


class TupleDomainSet(ComplexDomainSet):
    def __init__(self, typ):
        finite = all(isinstance(t.domain, DomainSet) and t.domain.finite for t in typ)
        super().__init__("Tuple", typ, finite=finite)

    def infcheck(self, x):
        if isinstance(x, collections.abc.Sequence) and not isinstance(x, str):
            if len(self.type) != len(x):
                return False
            return all(x[i] in self.type[i].domain for i in range(len(self.type)))
        else:
            return False

    def __len__(self):
        if not self.finite:
            raise ValueError("Non-finite `TupleDomainSet`s do not have a length.")
        elif len(self.type) == 0:
            # need to special case this -- the functools.reduce call will crash
            return 1
        else:
            return functools.reduce(lambda x, y: x*y, (len(t.domain) for t in self.type))

    def normalize(self, x):
        return tuple(self.type[i].domain.normalize(x[i]) for i in range(len(x)))

    def __iter__(self):
        domains = (t.domain for t in self.type)
        for p in itertools.product(*domains):
            yield p

    def enumerable(self):
        # the non-finite case is not supported for now
        return self.finite

    def element_repr(self, x, rich=False, **kwargs):
        return f"({','.join(self.type[i].domain.element_repr(x[i], rich=rich) for i in range(len(x)))})"

    def __repr__(self):
        return f"TupleDomainSet({self.type})"

    @classmethod
    def element_to_type(cls, x, ctrl):
        if isinstance(x, collections.abc.Sequence) and not isinstance(x, str):
            types = [ctrl(k) for k in x]
            for i in range(len(types)):
                if types[i] is None:
                    raise parsing.ParseError(f"Unknown type domain element in tuple: `{repr(x[i])}`")
            return TupleType(*types)
        return None


class TupleType(TypeConstructor):
    domain_class = TupleDomainSet
    """Type for tuples.  See `lang.Tuple`."""
    def __init__(self, *signature):
        #if len(signature) == 0:
        #    raise ValueError("Tuple type can't be 0 length")
        self.signature = tuple(signature)
        super().__init__()

    def copy_local(self, *sig):
        return TupleType(*sig)

    def functional(self):
        return False

    def check(self, x):
        raise NotImplementedError()

    def __repr__(self):
        return "(%s)" % ",".join([str(self.signature[i])
                                        for i in range(len(self.signature))])

    def latex_str(self, **kwargs):
        return ensuremath("\\left(%s\\right)" % ", ".join(
            [self.signature[i].latex_str()
                                    for i in range(len(self.signature))]))

    def __len__(self):
        return len(self.signature)

    def __getitem__(self, i):
        return self.signature[i]

    def __iter__(self):
        return iter(self.signature)


    def _type_eq(self, other):
        if not isinstance(other, TupleType):
            return False
        if len(self.signature) != len(other.signature):
            return False
        return all((self.signature[i]._type_eq(other.signature[i])
                                        for i in range(len(self.signature))))

    def _type_hash(self):
        # converting to tuple is necessary: generators hash but their hash
        # is not determined by (what would be their) content!
        return hash(tuple(t._type_hash() for t in self.signature))

    def __call__(self, other):
        return FunType(self, other)

    def _repr_latex_(self):
        return self.latex_str()

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "(")
        if next is None:
            return (None, i)
        else:
            i = next
            signature = []
            while i < len(s) and s[i] != ")":
                (m, i) = parse_control_fun(s, i)
                signature.append(m)
                if i >= len(s) or s[i] == ")":
                    break
                # this error message shouldn't actually arise.
                i = parsing.consume_char(s, i, ",", "Missing comma in type")
            i = parsing.consume_char(s, i, ")", "Unmatched ( in tuple type")
            return (TupleType(*signature), i)       

    @classmethod
    def random(cls, random_ctrl_fun):
        tuple_len = random.randint(0, random_len_cap)
        args = tuple([random_ctrl_fun() for i in range(0,tuple_len)])
        return TupleType(*args)

vartype_regex_str = r"[XYZ]('+|([0-9]*))"
vartype_regex = re.compile(vartype_regex_str)
vartype_regex_full = re.compile( "^" + vartype_regex_str + "$")

def is_vartype_symbol(x):
    m = vartype_regex_full.match(x)
    if m:
        return True
    else:
        return False

def parse_vartype(x):
    m = vartype_regex_full.match(x)
    if not m:
        return (None, None)
    symbol = x[0]
    if len(x) > 1:
        if x[1] == "'":
            return (symbol, len(x)-1)
        else:
            return (symbol, int(x[1:]))
    else:
        return (symbol, 0)

########
#
# type assignment code
#
########


# A type assignment is a dict where every entry maps a variable to a type.  That
# type may be itself a variable, or some other type. Each variable determines an
# equivalence class of variables that potentially map to one non-variable type.
#
# Constraints:
#   Type mapping chains are linear (i.e. cannot loop).
#   Variable types are represented in at most one chain.
#   No variable can map to an expression that contains an instance of itself.
#   (The so-called "occurs" check.)
#   Non-variable types should be at the end of chains.

def transitive_add(v, end, assignment):
    """Add something to the end of an existing chain.

    Doesn't check whether `end` is already present.
    """
    visited = set()
    while v in assignment:
        assert not (v in visited or v == end)
        visited |= {v}
        next_v = assignment[v]
        assignment[v] = end
        v = next_v
    return assignment

def transitive_find_end(v, assignment):
    """Find the end of an existing chain starting with `v`."""
    visited = set()
    last_v = None
    while isinstance(v, VariableType) and v in assignment:
        assert v not in visited
        visited.add(v)
        last_v = v
        v = assignment[v]
    return (v, last_v)

# 
def replace_in_assign(var, value, assign):
    """Replace all instances of `var` in the type assignment with `value`,
    including embedded instances and instances as a key.

    After this, `var` is *gone* from the assignment.  (Don't call this with
    var=value.)
    """
    if var in assign:
        if isinstance(value, VariableType):
            assert value not in assign
            if value != assign[var]:
                assign[value] = assign[var]
            else:
                del assign[value]
        del assign[var]
    dellist = list()
    for k in assign.keys():
        if isinstance(assign[k], VariableType) and assign[k] == var:
            if k != value:
                assign[k] = value
            else:
                dellist.append(k)
        else:
            try_subst = assign[k].sub_type_vars({var: value},
                                                        trans_closure=False)
            assign[k] = try_subst
    for d in dellist:
        del assign[d]
    return assign

def type_assignment_set_unsafe(assign, var, value):
    """Sets the end of a chain beginning with `var`.

    if the end of the chain is not a variable type, it is replaced with `value`.
    if it is a variable type, `value` goes on the end.
    if `var` isn't present, it is added.

    This function first substitutes any variables in `value` with the current
    assignment, which could result in failure.
    """
    try_subst = value.sub_type_vars(assign, trans_closure=True)
    if try_subst is None:
        return None
    if try_subst in assign:
        # value converts to a variable already present in the assignment.
        return assign
    if var in assign:
        (principal, prev) = transitive_find_end(var, assign)
        if isinstance(principal, VariableType):
            assign[principal] = value
        else:
            # this is the unsafe part
            assign[prev] = value
    else:
        assign[var] = value
    return assign

def type_assignment_get(assign, var):
    """Return the principal type for `var` in the assignment, or None if there
    is none."""
    (v, prev) = transitive_find_end(var, assign)
    if prev is None:
        return None
    else:
        return v

def union_assignment(assign, var, value):
    """Either add `value` to the assignment, or disjoin it to an existing
    assignment.

    (This will throw an exception if `value` or the existing assignment contain
    variables.)
    """
    cur = type_assignment_get(assign, var)
    if cur is not None and not isinstance(cur, VariableType):
        value = DisjunctiveType.factory(cur, value) # may throw exception
    if value is not None:
        type_assignment_set_unsafe(assign, var, value)
    return assign

def union_assignments(a1, a2):
    """Produce the union of two assignments using disjunctive types."""
    a1 = a1.copy()
    for m in a2:
        union_assignment(a1, m, a2[m])
    return a1


def debind(t, vars=None):
    while isinstance(t, Forall):
        t = t.debind(vars=vars)
    if not t._sublet:
        return t
    return t.copy_local(*[debind(sub, vars=vars) for sub in t])


class Forall(TypeConstructor):
    """Unary type constructor that indicates explicit unselective binding of
    any type variables in its scope."""

    def __init__(self, arg):
        self.arg = compact_type_vars(arg, fresh_only=True)
        TypeConstructor.__init__(self)

    def __len__(self):
        return 1

    def __getitem__(self, i):
        return (self.arg,)[i]

    def __iter__(self):
        return iter((self.arg,))

    def init_type_vars(self):
        self._type_vars = set()
        self._sublet = True

    def bound_type_vars(self):
        return set()

    def trivial(self):
        return not self.arg.bound_type_vars()

    def normalize(self):
        t = self
        while isinstance(t.arg, Forall):
            # debind would accomplish this, but it will rename variables too.
            # only do so if needed.
            t = t.arg

        # n.b. these two conditions make something like ∀<e,∀X> normalize to
        # ∀<e,X>. Would it be better to go to <e,∀X>?
        if t.arg.is_let_polymorphic():
            with no_new_type_vars():
                return Forall(debind(t.arg))
        if t.trivial():
            return t.arg
        return t

    def debind(self, vars=None):
        if vars is not None:
            assignment = dict()
        else:
            assignment = None
        r = freshen_type(self.arg, assignment=assignment)
        if vars is not None:
            vars = vars.update(set(assignment.values()))
        return r

    def functional(self):
        return self.arg.functional()

    @property
    def left(self):
        # ensure any variables get rebound
        # XX this gets a weaker constraint than the type encodes, should this
        # and `right` just error?
        return Forall(self.arg.left).normalize()

    @property
    def right(self):
        # ensure any variables get rebound
        # XX note on `left`
        return Forall(self.arg.right).normalize()

    def copy_local(self, arg):
        return Forall(arg)

    def check(self, x):
        raise self.arg.check(x)

    def sugar(self):
        return False
        # syntactic sugar: ∀X (for any X) reprs as `?` (and parses)
        return isinstance(self.arg, VariableType)

    def __repr__(self):
        if self.sugar():
            return "?"
        return f"∀{repr(self.arg)}"

    def _type_eq(self, other):
        if isinstance(other, Forall):
            return self.arg._type_eq(other.arg)
        else:
            return False

    def _type_hash(self):
        return (hash("∀") ^ self.arg._type_hash())

    def latex_str(self, **kwargs):
        if self.sugar():
            return ensuremath("?")
        return ensuremath(f"\\forall{{}}{self.arg.latex_str()}")

    def _repr_latex_(self):
        return self.latex_str()

    def unify(self, t2, unify_control_fun, assignment=None):
        rebind = False

        to_compact = set()
        left = debind(self, vars=to_compact)
        right = debind(t2, vars=to_compact)

        # to get this result we have to override AST ordering (!). The reason
        # is that we have to prioritize variables in the `right` argument now,
        # unconditionally. The default behavior will prioritize variables that
        # are on the right relative to the global ast, which may be the left
        # or the right here.
        # this is a bit like calling the main `unify` function instead of the
        # recursive one, especially given the finalization below.
        result, assignment = unify_control_fun(left, right, assignment=assignment, swap=False)
        if result is None:
            return (None, assignment)

        # finalize any local type mappings inferred during recursion. XX code
        # dup with `unify_details`...
        result = result.sub_type_vars(assignment, trans_closure=True)

        # if unify inferred a mapping from a type variable in the input to one
        # of the newly introduced fresh types, that fresh type has been made
        # concrete and can't be rebound
        for k in [k for k in assignment if k not in to_compact]:
            to_compact = to_compact - assignment[k].bound_type_vars()

        # rebind any mapped types in the assignment.
        # XX are there cases where fresh variables appear purely on the right
        # side of the map?
        assignment = {k: convex_rebind(assignment[k], to_compact) for k in assignment
                            if k not in to_compact}
        return convex_rebind(result, to_compact), assignment

    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "∀")
        if next is None:
            return (None, i)
        else:
            i = next
            (arg, i) = parse_control_fun(s, i)
            # maybe a bit hacky to do this in parsing: if there are no type
            # variables at all, get rid of the ∀.
            return (Forall(arg).normalize(), i)

    @classmethod
    def random(cls, random_ctrl_fun):
        return Forall(random_ctrl_fun()).normalize()


class VariableType(TypeConstructor):
    """A type variable.  Variables are named with X, Y, Z followed by a number
    (or prime symbols).

    A type variable represents a (not-necessarily-finite) set of types."""

    def __init__(self, symbol, number=None):
        self.number = None
        super().__init__()
        if number is not None:
            self.symbol = symbol[0] 
            self.number = number
        else:
            (symbol, number) = parse_vartype(symbol)
            if symbol is None:
                raise TypeParseError("Can't parse variable type", s=symbol)
            self.symbol = symbol
            self.number = number
        self.number = max(0, self.number)
        self.name = symbol
        if self.number == 0:
            self._key_str = str(self.symbol)
        else:
            self._key_str = f"{self.symbol}{self.number}"
        self.domain = set()
        self.init_type_vars()

    def internal(self):
        return self.symbol[0] == "I"

    def functional(self):
        """Return True, because there are functions in the set a type variable
        represents.  Particular assignments could rule this out, of course."""
        return True

    def copy_local(self):
        return VariableType(self.symbol, self.number)
    
    def unify(self, t2, unify_control_fun, assignment=None):
        """Unify `self` with `t2`.  Getting this right is rather complicated.

        The result is a tuple of a principal type and an assignment.
        The principal type for two (potentially variable) types is the strongest
        type compatible with both. If it fails, the left element of the return
        tuple will be None, and the relevant may be None. This isn't generally
        safe from side-effects on the input assignment.  If The return value
        has `None` as the right element, the input should be discarded.
        """

        # pre-check: if we are token identical, it doesn't matter what gets
        # returned
        if self == t2:
            return (self, assignment)

        # 1. find the principal type in the equivalence class identified by
        #    self.  May return self if there's a loop.
        #    (Other sorts of loops should be ruled out?)
        if assignment is None:
            assignment = dict()
        if self in assignment:
            (start, prev) = transitive_find_end(self, assignment)
        else:
            start = self
            prev = None
        # 2. find the principal type in the equivalence class identified by t2.
        if isinstance(t2, VariableType) and t2 in assignment:
            (t2_principal, t2_prev) = transitive_find_end(t2, assignment)
        else:
            # note! things will go wrong if this can have bound types! If t2
            # is a Forall itself, the case is handled by that `unify` code, but
            # we still need to debind for embedded bound types.
            # XX this can leave stray mappings in the assignment when the
            # debound variables go away
            t2_principal = debind(t2)
            t2_prev = None
        new_principal = start
        # 3. perform an occurs check -- that is, check for recursive use of
        #    type variables.  (E.g. unifying X with <X,Y>.)
        if PolyTypeSystem.occurs_check(new_principal, t2_principal):
            raise OccursCheckFailure(t2_principal, new_principal)

        # 4. Deal with cases where `start` is a type variable.  This will end
        #    up with the only instance of `start` as a key in the assignment.
        #    (Or no instance, if `start` and `t2_principal` are equivalent.)
        if isinstance(start, VariableType):
            # 4-a. if t2 is not (equivalent to) a type variable itself,
            #      substitute any embedded type variables according to the
            #      assignment. occurs-check situations can arise after this
            #      substitution.  (Could this all be condensed down to one
            #      occurs check?)
            if not isinstance(t2_principal, VariableType):
                t2_principal = t2_principal.sub_type_vars(assignment,
                                                            trans_closure=True)
                if PolyTypeSystem.occurs_check(start, t2_principal):
                    raise OccursCheckFailure(t2_principal, new_principal)

            # 4-b. add `start` => `t2_principal` to the assignment.  
            #      We do this by first clearing out `start` entirely from the
            #      assignment and then mapping it directly to `t2_principal`.
            if start != t2_principal:
                assignment = replace_in_assign(start, t2_principal, assignment)
                assignment[start] = t2_principal
                new_principal = t2_principal
        # 5. Deal with cases where `t2_principal` is a type variable.
        if isinstance(t2_principal, VariableType):
            # 5-a. First make sure `start` is consistent with the assignment by
            #      doing any necessary substitutions.
            if not isinstance(start, VariableType):
                start = start.sub_type_vars(assignment, trans_closure=True)
                # TODO: do I need an occurs check here?  Hasn't come up in tons
                # of random testing, but I'm not confident.
            # 5-b. Then, map `t2_principal` to `start` in the assignment.
            #      Note: if both are variables, this step will undo step 4 to
            #      some degree.  Both are necessary because *TODO*
            if t2_principal != start:
                assignment = replace_in_assign(t2_principal, start, assignment)
                assignment[t2_principal] = start
                new_principal = start
        # 6. Deal with cases where neither are type variables, by recursing.
        if not (isinstance(start, VariableType) or isinstance(t2_principal,
                                                                VariableType)):
            new_principal, assignment = unify_control_fun(start, t2_principal,
                                                                    assignment)
            if new_principal is None:
                return (None, None)
        return (new_principal, assignment)

    def init_type_vars(self):
        # this will trigger on the initial call to TypeConstructor.__init__,
        # need to defer
        if self.number is not None:
            self._type_vars = set((self,))
        self._sublet = False
    
    def sub_type_vars(self, assignment, trans_closure=False):
        """find the principal type, if any, determined by the `assignment` for
        `self.

        If `trans_closure` is true, check full chains, otherwise just check
        immediate assignments.
        """
        if self in assignment:
            x = assignment[self]
            if trans_closure:
                visited = {self}
                while x in assignment:
                    if x in visited:
                        from lamb import meta
                        from lamb.meta import logger
                        logger.error(
                            "breaking loop in substitution (x: '%s', visited: '%s', , assignment: '%s')"
                            % (x, visited, assignment))
                        break
                    visited |= {x}
                    x = assignment[x]
            return x
        else:
            return self

    def _type_eq(self, other):
        """This implements token equality.  This is _not_ semantic equality due
        to type variable binding.
        """
        if isinstance(other, VariableType):
            return self._key_str == other._key_str
        else:
            return False

    def sort_key(self):
        return (self.symbol, self.number)

    def _type_eq(self, other):
        return isinstance(other, VariableType) and self._key_str == other._key_str

    def _type_hash(self):
        return hash(self._key_str)

    def is_fresh(self):
        return False

    def __repr__(self):
        # never use primes in the repr
        return self._key_str
    
    def latex_str(self, **kwargs):
        # XX the prime thing was cute, but I'm not sure it ends up being very
        # readable...
        if self.number > 3 or self.symbol == "?":
            return ensuremath(self.symbol + "_{" + str(self.number) + "}")
        else:
            return ensuremath(self.symbol + "'" * self.number)
    
    def _repr_latex_(self):
        return self.latex_str()
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        (m_group, new_i) = parsing.consume_pattern(s, i, vartype_regex)
        if m_group is None:
            return (None, i)
        else:
            return (VariableType(m_group), new_i)

    @classmethod
    def random(cls, random_ctrl_fun):
        primes = random.randint(0, 5)
        var = random.choice(("X", "Y", "Z"))
        return VariableType(var, number=primes)

    @classmethod
    def any(cls):
        return Forall(VariableType("X", 0))


@contextmanager
def no_new_type_vars():
    # using this is very often an extremely bad idea. Use it only if you are
    # *absolutely sure* that the wrapped code cannot leak fresh variables.
    maxid = UnknownType.max_identifier
    yield
    # not in a finally block! an exception will skip this
    UnknownType.max_identifier = maxid


class UnknownType(VariableType):
    """Class used internally for fresh types."""
    max_identifier = 0
    def __init__(self, force_num=None):
        if force_num is None:
            self.freshen()
        else:
            self.identifier = force_num
        super().__init__("?", number=self.identifier)

    def freshen(self):
        # XX this implementation is extremely simple, but very brute force...
        UnknownType.max_identifier += 1
        self.identifier = UnknownType.max_identifier

    @classmethod
    def fresh(cls):
        return UnknownType()

    def is_fresh(self):
        return True

    def __repr__(self):
        return f"?{self.identifier}"

    def latex_str(self, **kwargs):
        return ensuremath(f"?_{{{self.identifier}}}")

    def internal(self):
        # n.b. the return value compares equal to `self`; this can be used to
        # inspect the identifier
        return VariableType("?", number=self.identifier)

    def copy_local(self):
        return UnknownType(force_num=self.identifier)
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        next = parsing.consume_char(s, i, "?")
        if next is not None:
            num, next2 = parsing.consume_number(s, next)
            if num is None:
                # syntactic sugar: `?` parses to ∀X. It's a bit annoying to
                # handle it here, but the `?` prefix makes it hard to do
                # elsewhere
                return VariableType.any(), next
            else:
                return UnknownType(force_num=num), next2
        return None, i

    @classmethod
    def random(cls, random_ctrl_fun):
        return UnknownType()


# This is a slightly weird case in that there's no way to directly instantiate
# an element of this set; rather, MetaTerm fully resolves any disjunctively
# typed element to its actual type.
class DisjunctiveDomainSet(ComplexDomainSet):
    def __init__(self, typ):
        finite = all(t.domain.finite for t in typ.disjuncts)
        super().__init__("Disjunctive", typ, finite=finite)

    def infcheck(self, x):
        for t in self.type:
            if x in t.domain:
                return True
        return False

    # XX if this ever becomes instantiatable, a normalize implementation is needed

    def __repr__(self):
        return f"DisjunctiveDomainSet({self.type})"

    def __len__(self):
        if not self.finite:
            raise ValueError("Non-finite `DisjunctiveDomainSet`s do not have a length.")

        return sum(len(t.domain for t in self.type.disjuncts))

    def __iter__(self):
        if not self.finite:
            raise ValueError("Can't iterate over non-finite `DisjunctiveDomainSet`s.")
        for t in self.type.type_list:
            for elem in t.domain:
                yield elem

    def enumerable(self):
        # only the finite case is supported right now...
        return self.finite

    def element_repr(self, x, rich=False, **kwargs):
        # not very easy to call, but it's easy to implement
        for t in self.type:
            if x in t.domain:
                return t.domain.element_repr(x, rich=rich)
        raise ValueError(f"Invalid element of disjunctive type {self.type}: `{x}`")

    def normalize(self, x):
        for t in self.type:
            if x in t.domain:
                return t.normalize(x)
        raise ValueError(f"Invalid element of disjunctive type {self.type}: `{x}`")

    @classmethod
    def element_to_type(cls, x, ctrl):
        # could just call `ctrl`, if loops are prevented?
        return None

class DisjunctiveType(TypeConstructor):
    """Disjunctive types.

    These types represent finite sets of non-polymorphic types.  (Accordingly,
    disjunctions of variable types are disallowed.)"""
    domain_class = DisjunctiveDomainSet
    def __init__(self, *type_list, raise_s=None, raise_i=None):
        disjuncts = set()
        for t in type_list:
            if isinstance(t, DisjunctiveType):
                disjuncts.update(t.disjuncts)
            elif t.is_polymorphic():
                # this constraint is somewhat arbitrary, and could be
                # generalized. But, then unification would be more complicated.
                raise TypeParseError(
                    "Polymorphic types can't be used disjunctively.",
                    raise_s, raise_i)
            else:
                disjuncts.add(t)
        if len(disjuncts) <= 1:
            raise TypeParseError(
                "Disjunctive type must have multiple unique disjuncts",
                raise_s, raise_i)
        self.disjuncts = disjuncts
        # still sort for a canonical ordering
        self.type_list = sorted(self.disjuncts, key=repr)
        super().__init__()
        self.store_functional_info()
        
    def _type_eq(self, other):
        # no variable types allowed, it is safe to ignore `cache`
        if isinstance(other, DisjunctiveType):
            return self.disjuncts == other.disjuncts
        else:
            return False

    def _type_hash(self):
        # no variable types allowed, it is safe to ignore `cache`
        return hash(tuple(self.type_list))
        
    def __len__(self):
        return len(self.disjuncts)
    
    def __getitem__(self, i):
        return self.type_list[i]
    
    def __iter__(self):
        return iter(self.type_list)
        
    def __repr__(self):
        return "[" + "|".join([repr(t) for t in self.type_list]) + "]"
    
    def latex_str(self, **kwargs):
        # wrap in curly braces to ensure the brackets don't get swallowed
        return ensuremath("{\\left[%s\\right]}" % "\\mid{}".join(
            [self.type_list[i].latex_str()
                                    for i in range(len(self.type_list))]))
    
    # this works if b is a regular type or a disjunctive type.
    def __or__(self, b):
        return DisjunctiveType(self, b)
    
    def __and__(self, b):
        return poly_system.unify(self, b)

    def copy_local(self, *parts):
        return DisjunctiveType(*parts)

    @classmethod
    def factory(cls, *disjuncts):
        """returns a disjunctive type or a non-disjunctive type, as appropriate
        for `disjuncts`.

        `disjuncts`, when turned into a set, is:
           length 0: return None
          length 1: return the content
          length 2: return a DisjunctiveType for the disjuncts.
    
        If multiple disjuncts are DisjunctiveTypes, this could still fail,
        depending on what the union looks like.
        """
        r = set(disjuncts)
        if len(r) == 0:
            return None
        elif len(r) == 1:
            (r,) = r
            return r
        else:
            return DisjunctiveType(*r)

    # test case: tp("[<e,t>|<e,n>|<n,t>]").intersection_point(tp("<X,t>"),
    #                                       types.poly_system._unify_r, dict())
    #               should map X to [e|n].
    def intersection_point(self, b, unify_fun, assignment):
        if b in self.disjuncts:
            return (b, assignment)
        else:
            new_disjuncts = list()
            return_assign = assignment
            # assumption: type variables can't be part of a disjunctive type.
            for d in self.disjuncts:
                tmp_assignment = assignment.copy() # sigh
                (principal, tmp_assignment) = unify_fun(d, b, tmp_assignment)
                # Important note: we discard all the temporary assignments
                # *unless* the type disjunction is eliminated.
                if principal is None:
                    continue
                new_disjuncts.append(principal)
                return_assign = union_assignments(return_assign, tmp_assignment)
            result = self.factory(*new_disjuncts)
            if result is None:
                return (result, assignment)
            else:
                return (result, return_assign)
    
    def store_functional_info(self):
        l_set = set()
        r_set = set()
        # alternative: only set something if all disjuncts are functional?
        for d in self.disjuncts:
            if d.functional():
                l_set |= {d.left}
                r_set |= {d.right}
        self.left = self.factory(*l_set)
        self.right = self.factory(*r_set)

    def functional(self):
        return (self.left is not None)

    # returns a FunType characterizing the set of functional types contained in
    # self. Note! This is not guaranteed to produce an equivalent type -- it
    # is only guaranteed to produce a type that is equivalent in its left
    # argument!
    def factor_functional_types(self):
        return FunType(self.left, self.right)

    def intersection(self, b, unify_fun, assignment=None):
        """Calculate the intersection of `self` and type `b`.

        If `b` is a DisjunctiveType, this involves looking at the intersection
        of the types. Otherwise, it involves unifying `b` with the contents of
        self and seeing what is left. Will return some type (not necessarily
        disjunctive) if it succeeds, otherwise None.
    
        Some examples:
            [e|n] intersect e = e
            [e|n] intersect X = [e|n]
            [<e,t>|<n,t>|<e,e>] intersect <X,t> = [<e,t>|<n,t>]
            [e|n] intersect t = None
        """
        if assignment is None:
            assignment = dict()
        if isinstance(b, DisjunctiveType):
            # this relies on type variables not being possible as disjuncts.
            # otherwise, you'd need to use unify to check equality.
            intersection = self.disjuncts & b.disjuncts
            return (self.factory(*intersection), assignment)
        else:
            return self.intersection_point(b, unify_fun, assignment)

    def resolve_element_type(self, e):
        # XX why is this on the type and not the domain?
        # if `e` is not a type domain element, guaranteed to return None
        for t in self.type_list:
            if e in t.domain:
                return t
        return None

    def unify(self, b, unify_control_fun, assignment=None):
        return self.intersection(b, unify_control_fun, assignment)
    
    @classmethod
    def parse(cls, s, i, parse_control_fun):
        starting_i = i
        next = parsing.consume_char(s, i, "[")
        if next is None:
            return (None, i)
        else:
            i = next
            signature = []
            # sequences like `[e|t|]` are valid, should they be?
            while i < len(s) and s[i] != "]":
                (m, i) = parse_control_fun(s, i)
                signature.append(m)
                # break on upcoming ].
                if i < len(s) and s[i] == "]":
                    break
                # error handling: if we have >1 disjuncts error on missing ],
                # otherwise error on missing |
                if i >= len(s) and len(signature) > 1:
                    break
                i = parsing.consume_char(s, i, "|",
                                            "Missing | in disjunctive type")
            # note: if there's a missing type in an expression like `[e|`, we
            # slightly misleadingly produce this error..
            i = parsing.consume_char(s, i, "]",
                                            "Unmatched [ in disjunctive type")
            return (DisjunctiveType(*signature, raise_s=s, raise_i=starting_i),
                                                                            i)
    
    @classmethod
    def random(cls, random_ctrl_fun):
        type_len = random.randint(2, random_len_cap)
        args = set()
        success = False
        while not success:
            # a lot of seeds might just not work for this class, so keep
            # trying until we get something sensible
            # TODO: in extremely simple (non-realistic) type systems this could
            # loop indefinitely.
            args = set([random_ctrl_fun() for i in range(0,type_len)])
            try:
                result = DisjunctiveType(*args)
            except TypeParseError:
                #print("retry", repr(args))
                continue
            success = True
        return result

####################
#
# Type systems and various utility stuff.
#
####################


class TypeSystem(object):
    """Parent class for a type system.  A TypeSystem provides:
     * unification functions for variables and function application
     * an identity criteria
     * some FA checking utilities
    """
    def __init__(self, name=None, atomics=None, nonatomics=None):
        self.name = name
        if self.name is None:
            self.raisemsg = "function-argument combination"
        else:
            self.raisemsg = name +  " function-argument combination"
        self._parse_cache = dict()
        self.atomics = set()
        if atomics is not None:
            for a in atomics:
                self.add_atomic(a)
        self.nonatomics = set()
        if nonatomics is not None:
            for a in nonatomics:
                self.add_nonatomic(a)

    def get_domain_prefixes(self):
        prefixes = {}
        for a in self.atomics:
            try:
                prefixes[a.domain.prefix] = a
            except AttributeError:
                pass
        return prefixes

    def add_atomic(self, atomic):
        if not atomic in self.atomics:
            try:
                # basic check to ensure non-overlapping type domains for
                # domains that use strings
                prefixes = self.get_domain_prefixes()
                if atomic.domain.prefix in prefixes.keys():
                    raise ValueError(f"Domain prefix `{atomic.domain.prefix} already used in type `{prefixes[atomic.domain.prefix]}`")
            except AttributeError:
                pass
            self._parse_cache[atomic.regex] = atomic
            self.atomics.add(atomic)

    def get_element_type(self, element, setfun=False):
        # Dead simple. Assumption: no overlapping types
        # TODO: some form of subtyping might be interesting
        for t in self.atomics:
            if element in t.domain:
                return t
        for t in self.nonatomics:
            if t.domain_class is not None:
                e_type = t.domain_class.element_to_type(element,
                    ctrl=functools.partial(self.get_element_type, setfun=setfun))
                if e_type is not None:
                    if isinstance(e_type, SetType) and setfun:
                        # convert a set into its characteristic function
                        e_type = FunType(e_type.content_type, type_t)
                        if not element in e_type.domain:
                            # should be impossible...
                            raise ValueError("Set is absent from corresponding characteristic function domain??")
                    return e_type

        return None

    def remove_atomic(self, atomic):
        if atomic in self.atomics:
            self.atomics.remove(atomic)
            del self._parse_cache[atomic]

    def add_nonatomic(self, na):
        self.nonatomics.add(na)

    def remove_nonatomic(self, na):
        self.nonatomics.remove(na)

    def atomic_parser(self, s, i):
        # note: no checking for multiple matches...
        for r in self._parse_cache.keys():
            (m_group, new_i) = parsing.consume_pattern(s, i, r)
            if m_group is None:
                continue
            return (self._parse_cache[r], new_i)
        raise TypeParseError("Unknown atomic type", s, i)

    def type_parser_recursive(self, s, i=0):
        for na in self.nonatomics:
            result, next = na.parse(s, i, self.type_parser_recursive)
            if result is not None:
                # one of the non-atomics succeeded
                return (result, next)
        # none of the non-atomics succeeded, so try atomic parser.
        if i >= len(s):
            raise TypeParseError("Missing type", s, i)
        (result, i) = self.atomic_parser(s, i)
        # may return None?
        return (result, i)

    def type_parser(self, s, require_exact_type=False):
        try:
            (r, i) = self.type_parser_recursive(s)
            if require_exact_type and i < len(s):
                raise TypeParseError("Extraneous characters in type", s=s, i=i)
            return r
        except parsing.ParseError as e:
            # TODO: raise this directly?
            raise TypeParseError(e.msg, s=e.s, i=e.i).with_traceback(e.__traceback__) from None

    def parse(self, s, require_exact_type=False):
        return self.type_parser(s, require_exact_type=require_exact_type)

    def fun_arg_check_bool(self, fun, arg):
        return (fun.type.functional() and
                self.type_allowed(fun.type) and
                self.type_allowed(arg.type) and
                self.eq_check(fun.type.left, arg.type))

    def check_type(self, t):
        return (t in self.atomics or t.__class__ in self.nonatomics)

    def _unify_r(self, a, b, assignment=None):
        if not (self.check_type(a) and self.check_type(b)):
            return None
        (result, r_assign) = a.unify(b, self._unify_r)
        return result

    def unify(self, t1, t2, assignment=None):
        r = self.unify_details(t1, t2, assignment=assignment)
        if r is None:
            return None
        return r.principal

    def unify_details(self, t1, t2, assignment=None, show_failure=False):
        # assignment is unused here
        if not show_failure and (cached := get_unify_cached(t1, t2)) is not None:
            return cached

        result = self._unify_r(t1, t2)
        if result is None and not show_failure:
            return None
        # unification in this system is very straightforward: if a type is
        # found, it is the principal type.
        return UnificationResult(result, t1, t2)

    def unify_ar(self, arg, ret, assignment=None):
        return FunType(arg, ret)

    def unify_fr(self, fun, ret, assignment=None):
        if fun.functional():
            r = self.unify(fun.right, ret)
            if r is None:
                return (None, None, None)
            else:
                return (fun, fun.left, r)
        else:
            return (None, None, None)

    def unify_fa(self, fun, arg, assignment=None):
        """Try unifying the input type of the function with the argument's type.
        If it succeeds, it returns a (possibly changed) tuple of the function's
        type, the argument's type, and the output type. If this fails, returns
        (None, None, None)."""

        if fun.functional():
            a = self.unify(fun.left, arg)
            if a is None:
                return (None, None, None)
            else:
                return (fun, a, fun.right)
        else:
            return (None, None, None)

    def fun_arg_check(self, fun, arg):
        if not self.fun_arg_check_bool(fun, arg):
            raise TypeMismatch(fun.type, arg.type,
                                            "function-argument combination")

    def eq_check(self, a, b):
        result = self.unify(a,b)
        return (result is not None)

    def type_allowed(self, a):
         return True

    def latex_str(self, **kwargs):
        return "Type system with atomic types: " + ensuremath(", ".join(
                                        [a.latex_str() for a in self.atomics]))

    def _repr_latex_(self):
        return self.latex_str()

    def random_type(self, max_depth, p_terminate_early, nonatomics=None):
        term = random.random()
        if max_depth == 0 or term < p_terminate_early:
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1,
                                                            p_terminate_early)
            if nonatomics is None:
                nonatomics = list(self.nonatomics)
            t_class = random.choice(nonatomics)
            return t_class.random(ctrl_fun)

    def repr_check(self, t):
        return (t == self.type_parser(repr(t)))

    def repr_unify_check(self, t):
        result = self.unify(t, self.type_parser(repr(t)))
        return (result is not None)

    def unify_check(self, t1, t2):
        result = self.unify(t1, t2)
        return (result is not None)

    def parse_unify_check(self, t1, t2):
        return self.unify_check(self.type_parser(t1), self.type_parser(t2))

    def modify_domains(self, m):
        from lamb.meta import Model
        if isinstance(m, Model):
            m = m.domains
        for t in m:
            if t not in self.atomics:
                raise ValueError(f"Unknown type {t} in domain modification")
        for typ in m:
            typ.modify_domain(m[typ])

    def reset_domains(self):
        for typ in self.atomics:
            typ.reset_domain()


########################
#
# Polymorphic type system
#
########################

# first some more basic functions for manipulating and testing assignments.

def injective(d):
    """Is `d` an injective assignment?  I.e. does it map all keys onto
    distinct values? `d` must map to hashable values."""

    # implementation: count the unique mappings.
    return len(d.keys()) == len(set(d.values()))

def invert(d):
    """Try to invert the assignment `d`.  Will throw an exception if the
    assignment is not injective."""
    i = dict()
    for k in d.keys():
        if d[k] in i:
            raise Exception("can't invert non-injective dict")
        i[d[k]] = k
    return i

def strengthens(d):
    """Check for any strengthening assignments in `d`.  A strengthening
    assignment is one that maps a variable to a non-variable."""
    for key in d:
        # XX bound types are a bit weird here, but the behavior still seems
        # right?
        if not isinstance(d[key], VariableType):
            return True
    return False

def safe_vars(typ, var_list):
    """Returns a mapping from type variables in `typ` to variable names that
    are safe from collision from `var_list`."""
    unsafe = typ.bound_type_vars()
    base_nums = dict()
    result = dict()
    for base in var_list:
        if base in unsafe:
            base_letter = base.symbol[0]
            if base_letter not in base_nums:
                base_nums[base_letter] = 0
            # TODO this is not very efficient
            vt = VariableType(base_letter, number=base_nums[base_letter])
            while vt in unsafe:
                base_nums[base_letter] += 1
                vt = VariableType(base_letter, number=base_nums[base_letter])
            result[base] = vt
            unsafe = unsafe | {vt}
        else:
            unsafe = unsafe | {base}
    return result

def vars_in_env(type_env, keys=False):
    """Where `type_env` is a mapping to types, return all type variables found
    in the mapping. If `keys` is true, collect all keys."""
    unsafe = set()
    for k in type_env:
        if keys:
            unsafe |= {k}
        unsafe |= type_env[k].bound_type_vars()
    return unsafe

def safe_var_in_set(unsafe, internal=False, n=0):
    """Find a safe type variable relative to set `unsafe`.  

    This will be prefixed with `X` unless `internal`=True, in which case the
    prefix is `I`.
    """
    if internal:
        symbol = "I"
    else:
        symbol = "X"
    vt = VariableType(symbol, n)
    while vt in unsafe:
        n += 1
        vt = VariableType(symbol, n)
    return vt

def fresh_for(*types, unsafe=None, internal=False, n=1):
    """Find `n` fresh type variables relative to any types in `types`, and/or
    a set of type variables provided by `unsafe`. The elements of `types` may
    be arbitrary polymorphic types."""

    # unused: written for some code that has not yet worked out to try to
    # improve type freshening. However, this code was reasonably well-tested
    # in the process.
    l = []
    var_n = 0
    if unsafe is None:
        unsafe = set()
    all_unsafe = unsafe.union(*[t.bound_type_vars() for t in types])

    for i in range(n):
        l.append(safe_var_in_set(all_unsafe, internal=internal, n=var_n))
        all_unsafe.add(l[-1])
        var_n = l[-1].number
    return l

def make_safe(typ1, typ2, unsafe=None):
    """Return a version of typ1 that is completely safe w.r.t. variables in
    typ2.

    Note that this will work in either order to avoid variable name collisions,
    but preserves variable names in typ2 over typ1.
    """
    if unsafe is None:
        unsafe = list()
    else:
        unsafe = list(unsafe)
    assignment = safe_vars(typ2, list(typ1.bound_type_vars()) + unsafe)
    return typ1.sub_type_vars(assignment)

def compact_type_set(types, unsafe=None, fresh_only=False):
    """Given some set of variables `types`, produce a mapping to more compact
    variable names. Try to keep any lower-numbered type variables.

    If `unsafe` is set, avoid types in `unsafe`.
    """
    if unsafe is None:
        unsafe = set()
    remap = list()
    keep = set()
    mapping = dict()
    for t in types:
        # XX this will probably crash on non-variables, more sensible handling?
        if t.is_fresh() or not fresh_only and t.number > 3:
            remap.append(t)
        else:
            keep.add(t)
    remap.sort(key=lambda x : (x.symbol, x.number)) # for deterministic behavior
    for t in remap:
        m = safe_var_in_set(keep | unsafe)
        assert t not in m
        mapping[t] = m
        keep.add(m)
    return mapping


def freshen_type_set(types):
    """Produce a mapping from variables in `types` to fresh type variables."""

    # XX it would be nice to move away from using this method for fresh vars,
    # but it is extremely tricky to get anything more minimal right

    # we need to sort in order to get a deterministic freshening order
    # XX should this use AST position?
    types = sorted(types, key=lambda x: (x.symbol, x.number))
    return {t: UnknownType() for t in types}


def freshen_type(t, assignment=None):
    f = freshen_type_set(t.bound_type_vars())
    if assignment is None:
        assignment = f
    else:
        assignment.update(f)
    return t.sub_type_vars(assignment)


def compact_type_vars(t, unsafe=None, fresh_only=False):
    """Compact the type variables in `t` so as to make them more
    readable."""

    return t.sub_type_vars(compact_type_set(t.bound_type_vars(), unsafe,
                                            fresh_only=fresh_only))


# given some type var set, if there is a segment of `t` that contains only
# vars from that set, and no other part of `t` contains such vars, then bind
# that segment universally.
def convex_rebind(t, to_compact):
    if not t.bound_type_vars():
        return t
    elif all(v in to_compact for v in t.bound_type_vars()):
        # if t contains all and only vars from `to_compact`, we have found
        # something to rebind.
        return Forall(compact_type_vars(t)).normalize()
    elif not len(t):
        # if t is a relevant type var, the prior clause will have handled it
        return t

    # are there parts of `t` that have subsets of the targeted type vars that
    # are present only in that part?
    # a part is potentially compactable if it has some of the targeted type
    # vars at all. But, binding all of these unselectively would produce the
    # wrong result in some cases. Example: <?1,<X,?1>> where to_compact={?1}.
    # This example isn't expressible with purely unselective binding, since
    # <∀X,<X,∀X>> is a weaker type, but ∀<Y,<X,Y>> binds a non-targeted
    # variable (that the caller may need). For cases like this, we will leave
    # the ? variables to the mercy of global binding.
    # However, we can and should still do something with cases like
    # t=<?1,<X,?2>> with to_compact={?1, ?2}.
    # (specific case to look at: `unify(tp('<∀X,<Y,∀X>>'), tp('∀<X,<Y,X>>'))`)
    # Here, the type *is* equivalent to <∀X,<X,∀X>>. Since t[0] and t[1] contain
    # fully disjoint subsets of to_compact, we can recurse to find the individual
    # type variables. On the recursive call, binding only happens if the part
    # is completely convex wrt to_compact. (If a type variable occurs only
    # once, this at least can happen when you get to the individual variable.)
    # this step does *not* check other type vars, just convexity; the check on
    # other variables is handled immediately on recursion (above).
    could_compact = [(to_compact & p.bound_type_vars()) for p in t]
    disjoint = [None] * len(could_compact)
    # for any i,j check whether t[i] and t[j] are disjoint on vars in `to_compact`
    # this is somewhat annoying to do in a general way, and the below uses a
    # dynamic programming approach to fill in `disjoint`. In practice, we are
    # mostly dealing with len 2 types, for which this approach is
    # over-complicated, but tuple types can be arbitrary length.
    for i in range(len(could_compact)):
        if disjoint[i] is not None and not disjoint[i] or not could_compact[i]:
            continue
        for j in range(i+1, len(could_compact)):
            if len(could_compact[i] & could_compact[j]):
                # mark both i and j as overlapping with something
                disjoint[i] = disjoint[j] = False
        if disjoint[i] is None:
            # we've found no overlaps for i
            disjoint[i] = True

    if any(disjoint):
        l = list(t)
        dirty = False
        for i in range(len(disjoint)):
            if disjoint[i]:
                l[i] = convex_rebind(t[i], to_compact)
                dirty = dirty or l[i] is not t[i]
        if dirty:
            return t.copy_local(*l)
    return t


enable_cache = True
_unify_cache = {}


def update_unify_cache(result):
    global _unify_cache
    # type variable unification is semantically, but not syntactically,
    # symmetric. That is, unify(X,Y) = X, but unify(Y,X) = Y. To ensure
    # deterministic results, for now we do not cache the symmetric pair
    # if the principal type is polymorphic. (If it isn't, this should be safe..)
    symmetric = not result.is_polymorphic()
    t1, t2 = result.cache_values()
    if t1 not in _unify_cache:
        _unify_cache[t1] = {}
    if symmetric and t2 not in _unify_cache:
        _unify_cache[t2] = {}
    # print(f"unify cache: {result.t1} + {result.t2} => {result.principal}")
    _unify_cache[t1][t2] = result
    if symmetric:
        _unify_cache[t2][t1] = result


def reset_unify_cache():
    global _unify_cache
    _unify_cache = {}


def get_unify_cached(t1, t2):
    if not enable_cache:
        return None
    t1 = CachableType(t1)
    if t1 not in _unify_cache:
        return None
    return _unify_cache[t1].get(CachableType(t2), None)


class UnificationResult(object):
    """Wrapper class for passing around unification results."""
    def __init__(self, principal, t1, t2, mapping=None, update_cache=True):
        if mapping is None:
            mapping = dict()
        self.principal = principal
        self.t1 = t1
        self.t2 = t2
        self.mapping = mapping
        # currently unused, but this would allows for checking of alpha
        # equivalence during unification
        self.trivial = injective(mapping) and not strengthens(mapping)

        # XX possibly not  worth caching when any of the ingredients have
        # fresh variables. Compacting might work?
        update_cache = update_cache and enable_cache
        if update_cache and principal is not None and not self.principal.has_fresh_variables():
            update_unify_cache(self)

    def cache_values(self):
        return CachableType(self.t1), CachableType(self.t2)

    def is_polymorphic(self):
        """Is the principal type polymorphic?"""
        # note! polymorphic input types can unify to a non-polymorphic
        # principle type, e.g. unify(<X,e>,<e,X>) = <e,e>
        return self.principal is not None and self.principal.is_polymorphic()

    def _repr_html_(self):
        s = "<table><tr><td>Principal type:&nbsp;&nbsp; </td>"
        if self.principal is None:
            # XX this formatting might not work right in colab
            s += "<td><span style=\"color:red\">Unification failure!</span></td></tr>"
        else:
            s += f"<td>{self.principal.latex_str()}</td></tr>"
        s += f"<tr><td>Inputs: </td><td>{self.t1.latex_str()} and {self.t2.latex_str()}</td></tr>"
        if self.principal is not None:
            s += f"<tr><td>Mapping: </td><td>{utils.dict_latex_repr(self.mapping)}</td></tr>"
        s += "</table>"
        return s

    def __repr__(self):
        # just the principal type
        return f"{repr(self.principal)}"

class PolyTypeSystem(TypeSystem):
    """A polymorphic type system.  

    This implements appropriate unification for type variables (in the
    Hindley-Milner type system) and disjunctive types.
    """
    def __init__(self, atomics=None, nonatomics=None):
        self.type_ranking = dict()
        super().__init__("polymorphic", atomics=atomics, nonatomics=nonatomics)
        # n.b. it is important that these two have exactly the same priority;
        # this allows unify input order to deterministically relate to output
        # order in certain key cases
        self.add_nonatomic(UnknownType, 10)
        self.add_nonatomic(VariableType, 10)
        self.add_nonatomic(Forall, 20)

    def add_nonatomic(self, t, ranking=0):
        super().add_nonatomic(t)
        self.type_ranking[t] = ranking

    def remove_nonatomic(self, t):
        supr().remove_nonatomic(t)
        del self.type_ranking[t]

    def add_atomic(self, t, ranking=0):
        super().add_atomic(t)
        self.type_ranking[t.__class__] = ranking

    def _unify(self, t1, t2):
        raise NotImplementedError

    def unify(self, t1, t2, assignment=None, allow_raise=False):
        if assignment is None:
            assignment = dict()

        if not assignment and (cached := get_unify_cached(t1, t2)) is not None:
            return cached.principal

        try:
            result = self.unify_details(t1, t2, assignment=assignment)
        except OccursCheckFailure as e:
            if allow_raise:
                raise e
            else:
                return None
        if result is None:
            return None
        else:
            return result.principal

    @classmethod
    def occurs_check(self, t1, t2):
        if isinstance(t1, VariableType) and not isinstance(t2, VariableType):
            return t1 in t2.bound_type_vars()
        if isinstance(t2, VariableType) and not isinstance(t1, VariableType):
            return t2 in t1.bound_type_vars()
        return False

    def unify_details(self, t1, t2, assignment=None, show_failure=False):
        """Find the principal type, if any, for `t1` and `t2`.

        If this succeeds, return a UnificationResult."""
        if assignment is None:
            assignment = dict()
        else:
            assignment = assignment.copy() # ugh

        # for now, no caching for calls that are under some type assignment;
        # we would need to factor this in to the caching
        use_cache = not assignment and not show_failure
        if use_cache and (cached := get_unify_cached(t1, t2)) is not None:
            return cached

        # note: the following may raise OccursCheckFailure!
        (result, r_assign) = self._unify_r(t1, t2, assignment=assignment)

        if result is None:
            if show_failure:
                # assignment is not informative in the case of a failure
                return UnificationResult(result, t1, t2)
            return None
        # a principal type has been found, but may not be fully represented by
        # result. This will happen if later parts of one type forced some
        # strengthening of assumptions, and we need to apply the stronger
        # assumption everywhere.
        result = result.sub_type_vars(r_assign, trans_closure=True)
        return UnificationResult(result, t1, t2, r_assign, update_cache=use_cache)

    def _unify_r_control(self, t1, t2, assignment, swap=False):
        # this setup is a bit convoluted, but the swap named parameter in this
        # and in _unify_r_swap is intended to let the controllee reset this
        # argument
        if swap:
            try:
                return self._unify_r(t2, t1, assignment=assignment)
            except TypeMismatch as e:
                e.swap_order()
                raise e
        else:
            return self._unify_r(t1, t2, assignment=assignment)

    def _unify_r_swap(self, t1, t2, assignment, swap=True):
        return self._unify_r_control(t1, t2, assignment, swap=swap)

    def _unify_r(self, t1, t2, assignment):
        """Recursive unification of `t1` and `t2` given some assignment.

        This is not really intended to be called directly; see comments in
        `unify_details` for more information.  Call `unify` or
        `unify_details`.

        On failure may return None (as the first element of a tuple) or
        raise."""
        if self.occurs_check(t1, t2):
            raise OccursCheckFailure(t1, t2)
        # Type rankings put type classes that have custom unification code
        # for polymorphism higher than those that don't. If t2 has a higher
        # or equal type ranking, let it drive unification. However, we provide
        # a control function that reverses back the order when recursing, so
        # that there's a stable order for comparison at all points in the AST.
        # Note: for the sake of simpler code, this does swap the order for
        # non-polymorphic equally-ranked types, but for such types, symmetry
        # is guaranteed. (Polymorphic unification is only symmetric up to
        # alphabetic variants.)
        if self.type_ranking[t1.__class__] <= self.type_ranking[t2.__class__]:
            # XX if t1=t2, the recursion could be short-circuited, but I'm
            # unclear if this is a useful optimization
            return t2.unify(t1, self._unify_r_swap, assignment=assignment)
        else:
            return t1.unify(t2, self._unify_r_control, assignment=assignment)

    def _build_hyp_fun(self, arg, ret):
        if arg is None:
            arg = Forall(VariableType('X', 0))
        if ret is None:
            ret = Forall(VariableType('X', 0))
        if isinstance(ret, Forall) and isinstance(arg, Forall):
            # for this case, we can safely scope ∀ over the whole thing (and
            # the results are better if we do so)
            return Forall(FunType(arg, ret)).normalize()
        else:
            return FunType(arg, ret)

    def unify_fun(self, fun, arg, ret, assignment=None):
        # the code below works for non-polymorphic types, but uses much
        # heavier infrastructure
        if not fun.is_polymorphic():
            if arg is not None and not arg.is_polymorphic() and ret is None:
                return super().unify_fa(fun, arg)
            elif ret is not None and not ret.is_polymorphic() and arg is None:
                return super().unify_fr(fun, ret)

        hyp_fun = self._build_hyp_fun(arg, ret)
        try:
            # order matters here
            result = self.unify_details(hyp_fun, fun, assignment=assignment)
        except OccursCheckFailure as e:
            if arg is None:
                e.error = f"Occurs check failure while trying to infer function type given return type {ret}"
            else:
                # assumption: one or the other is not None if we have reached here
                e.error = f"Occurs check failure while trying to infer function type given argument `{arg}`"
            e.swap_order()
            raise e

        if result is None: # `fun` is not a function or cannot be made into one
            return (None, None, None)
        else:
            principal = result.principal
            if isinstance(principal, Forall):
                # we can't sensibly access left/right, there's nothing for it
                # but to go to fresh types. (XX: refactor so that this is on
                # the caller to handle)
                principal = debind(principal)
            return (principal, principal.left, principal.right)

    def unify_fr(self, fun, ret, assignment=None):
        """Find principal types if `ret` is a return value for `fun`.

        Returns a triple of the principal types of the function, its left type,
        and its right type.  Returns (None, None, None) on failure."""

        return self.unify_fun(fun, None, ret, assignment=assignment)

    def unify_fa(self, fun, arg, assignment=None):
        """Find principal types if `ret` is a return value for `fun`.

        Returns a triple of the principal types of the function, its left type,
        and its right type.  Returns (None, None, None) on failure."""

        return self.unify_fun(fun, arg, None, assignment=assignment)

    def fun_arg_check_bool(self, fun, arg):
        f, a, r = self.unify_fun(fun.type, arg.type, None)
        return f is not None

    def alpha_equiv(self, t1, t2, mapping=None):
        """Are `t1` and `t2` alpha equivalents of each other?"""

        # two types t1 and t2 are alpha equivalents just in case they have
        # identical ASTs, and there's surjective+injective mapping from
        # variable types in t1 to types in t2 that preserves AST identity

        # note: there's a unify-based alternative that is arguably more general,
        # but also more costly (because it potentially involves a *lot* more
        # variable juggling). This would be to alpha rename any variable
        # collisions in t1 vs t2, run unify_details, and then check if the
        # resulting assignment is injective and non-strengthening (which
        # entails bijectivity). see UnificationResult.trivial.

        if mapping is None:
            # providing a mapping is primarily to let the caller see it if
            # desired
            mapping = {}

        if len(t1.bound_type_vars()) != len(t2.bound_type_vars()):
            # easy optimization: if t1 and t2 don't have the same number of
            # variables, there's no way for them to be alpha equivalents.
            return False

        def alpha_equiv_r(t1, t2):
            if not t1.is_polymorphic() and not t2.is_polymorphic():
                return t1 == t2
            elif isinstance(t1, VariableType) and isinstance(t2, VariableType):
                if t1 not in mapping:
                    mapping[t1] = t2
                elif t1 in mapping and mapping[t1] != t2:
                    return False
                return True
            else:
                # XX code dup with _type_eq
                if t1.__class__ != t2.__class__ or len(t1) != len(t2):
                    return False
                if isinstance(t1, Forall):
                    # intentional call to the outer alpha_equiv function! Any
                    # variables in these subtypes live in their own namespace,
                    # so we want to do this check independent of the current
                    # mapping.
                    # XX should X vs ∀X (etc) satisfy alpha equivalence??
                    return self.alpha_equiv(t1.arg, t2.arg)

                # for anything else, recurse to look for more type variables
                for i in range(len(t1)):
                    if not alpha_equiv_r(t1[i], t2[i]):
                        return False
            return True
        if alpha_equiv_r(t1, t2):
            # final check: did all variables get uniquely mapped?
            # we're guaranteed to have every variable in t1 present in the
            # mapping at this point, and the initial length check means that
            # we don't need to worry about missing any types in t2 (surjectivity
            # failures) as long as the mapping is injective.
            return injective(mapping)
        else:
            return False


    def compact_type_vars(self, t1, unsafe=None):
        """Compact the type variables in `t1` so as to make them more
        readable."""

        return compact_type_vars(t1, unsafe=unsafe)

    def unify_sym_check(self, t1, t2, require_unify=False):
        """Utility function for testing that unification obeys symmetry.

        Return true if `t1` and `t2` produce the same unification result
        (including failure) in both directions."""
        from lamb.meta import logger
        oldlevel = logger.level
        logger.setLevel(logging.CRITICAL) # suppress occurs check errors
        r1 = self.unify(t1, t2)
        r2 = self.unify(t2, t1)
        logger.setLevel(oldlevel)
        if ((r1 is None) and (r2 is None)):
            return not require_unify
        if ((r1 is None) or (r2 is None)):
            logger.error("Unify failed in one direction, results '%s' and '%s'"
                                                    % (repr(r1), repr(r2)))
            return False
        result = self.alpha_equiv(r1, r2)
        if result and require_unify:
            return r1 # return r1 as a principal type for this case
        return result

    def random_from_class(self, cls, max_depth=2, p_terminate_early=0.2,
                                                    allow_variables=False):
        return cls.random(self.random_ctrl(max_depth=max_depth,
                                           p_terminate_early=p_terminate_early,
                                           allow_variables=allow_variables))

    def random_ctrl(self, max_depth=2, p_terminate_early=0.2,
                                                    allow_variables=False):
        return lambda *a: self.random_type(max_depth - 1,
                                            p_terminate_early, allow_variables)

    def random_type(self, max_depth, p_terminate_early, allow_variables=True,
                                                        allow_disjunction=True,
                                                        nonatomics=None):
        """Generate a random type of `max_depth`."""
        if nonatomics is None:
            nonatomics = self.nonatomics
        term = random.random()
        if max_depth == 0 or term < p_terminate_early:
            # choose an atomic type
            t = random.choice(list(self.atomics))
            return t
        else:
            # choose a non-atomic type and generate a random instantiation of it
            ctrl_fun = lambda *a: self.random_type(max_depth - 1,
                                            p_terminate_early,
                                            allow_variables=allow_variables,
                                            allow_disjunction=allow_disjunction,
                                            nonatomics=nonatomics)
            options = nonatomics - {UnknownType}
            if not allow_variables:
                options -= {VariableType}
            if not allow_disjunction:
                options -= {DisjunctiveType}
            t_class = random.choice(list(options))
            return t_class.random(ctrl_fun)

    def random_variable_type(self, max_depth, p_terminate_early, nonatomics=None):
        """Generate a random type of `max_depth`; use only variable types in
        place of atomic types."""
        term = random.random()
        ctrl_fun = lambda *a: self.random_variable_type(max_depth - 1,
                                                            p_terminate_early,
                                                            nonatomics=nonatomics)
        if max_depth == 0 or term < p_terminate_early:
            # choose a variable type
            t = VariableType.random(ctrl_fun)
            return t
        else:
            if nonatomics is None:
                nonatomics = self.nonatomics
            # choose a non-variable type and generate a random instantiation
            t_class = random.choice(
                    list(nonatomics - {VariableType, DisjunctiveType, UnknownType}))
            return t_class.random(ctrl_fun)

class TypeMismatch(Exception):
    """Exception for type mismatches of all sorts."""
    def __init__(self, i1, i2, error=None, occurs_check=False, mode=None):
        self.i1 = i1
        self.i2 = i2
        self.occurs_check = occurs_check
        if is_type(i1):
            self.type1 = i1
        else:
            try:
                self.type1 = self.i1.type
            except AttributeError:
                self.type1 = "?"

        if is_type(i2):
            self.type2 = i2
        else:
            try:
                self.type2 = self.i2.type
            except AttributeError:
                self.type2 = "?"

        # mode is for backwards compatibility
        if error is None:
            error = mode
        if error is None:
            self.error = "unknown"
        else:
            self.error = error

    def swap_order(self):
        tmp = self.i1, self.type1
        self.i1, self.type1 = self.i2, self.type2
        self.i2, self.type2 = tmp

    def item_str(self, i, t, latex=False):
        from lamb.meta import TypedExpr, TypedTerm
        # this is hacky for now: if we are printing an error about a TypedExpr
        # we want the repr for markdown backticks, but for composition results
        # we want the latex code
        # XX this isn't working right in the continuations notebook...
        if isinstance(i, TypedExpr):
            latex = False
        if i is None:
            return None
        if is_type(i):
            if latex:
                return "type %s" % i.latex_str()
            else:
                return "type `%s`" % repr(i)
        elif isinstance(i, str):
            if t is None or t == "?":
                return f"`{i}`"
            else:
                if latex:
                    return "%s/%s" % (i, t.latex_str())
                else:
                    return "`%s`/%s" % (i, repr(t))
        else:
            # XX this will fail if this error path is triggered during package
            # loading
            from lamb.lang import Item
            # a TypedTerm's repr always shows the type right there, making
            # the longer form below redundant
            if (t is None or t == "?"
                                or isinstance(i, TypedTerm)
                                or isinstance(i, Item)):
                if latex and getattr(i, 'latex_str', None):
                    return f"{i.latex_str(suppress_parens=True)}"
                else:
                    return f"`{repr(i)}`"
            else:
                # assumption: type is shown as part of `i`, so it would be
                # redundant to print it
                if latex and getattr(i, 'latex_str'):
                    return f"{i.latex_str(suppress_parens=True)}/{t.latex_str()}"
                else:
                    return f"`{repr(i)}/{repr(t)}`"

    def __str__(self):
        return self.description(latex=False)

    def latex_str(self, **kwargs):
        return self.description(latex=True)

    def description(self, latex=False):
        is_1 = self.item_str(self.i1, self.type1, latex=latex)
        is_2 = self.item_str(self.i2, self.type2, latex=latex)
        if latex:
            tm_str = '<span style="color:red">**TypeMismatch**</span>'
        else:
            tm_str = "TypeMismatch"
        if is_1 is None:
            if is_2 is None:
                return "%s, unknown context (%s)" % (tm_str, self.error)
            else:
                return "%s on %s (%s)" % (tm_str, is_2, self.error)
        else:
            if is_2 is None:
                return "%s on %s (%s)" % (tm_str, is_1, self.error)
            else:
                return ("%s: %s and %s conflict (%s)"
                                            % (tm_str, is_1, is_2, self.error))

    def _repr_markdown_(self):
        return self.description(latex=True)

    def __repr__(self):
        return self.__str__()


class OccursCheckFailure(TypeMismatch):
    def __init__(self, t1, t2):
        super().__init__(t1, t2, occurs_check=True, error="Occurs check failed")


class TypeParseError(parsing.ParseError):
    """Exception for when types can't be parsed or generated correctly."""
    def __init__(self, msg, s, i):
        # simplified Type ParseError setup; don't use some of the fields
        super().__init__(msg, s=s, i=i)


def reset():
    global type_e, type_t, type_n, type_property, type_transitive
    global basic_system, poly_system

    basic_system = TypeSystem(atomics={type_e, type_t, type_n},
                              nonatomics={FunType, TupleType})
    poly_system = PolyTypeSystem(atomics={type_e, type_t, type_n},
                                 nonatomics={FunType, TupleType, SetType})
    poly_system.add_nonatomic(DisjunctiveType, 1)


def init():
    # don't reset these after the first init, so that the module-level
    # properties are stable
    global type_e, type_t, type_n, type_property, type_transitive
    type_e = BasicType("e")
    type_t = BasicType("t", BooleanSet())
    BooleanSet.type = type_t
    type_n = BasicType("n", SimpleNumericSet())
    SimpleNumericSet.type = type_n
    type_property = FunType(type_e, type_t)
    type_transitive = FunType(type_e, type_property)
    reset()


init()


import unittest
class TypeTest(unittest.TestCase):
    def setUp(self):
        reset()

    def test_parser_simple(self):
        for i in range(0, 1000):
            self.assertTrue(
                    basic_system.repr_check(basic_system.random_type(5, 0.2)))

    def test_parser_poly(self):
        for i in range(0, 1000):
            t = poly_system.random_type(5, 0.2)
            self.assertTrue(
                    poly_system.repr_check(t),
                    f"repr_check failure on random polymorphic system type {t}")

    def test_parser_poly_unify(self):
        for i in range(0, 1000):
            t = poly_system.random_type(5, 0.2)
            self.assertTrue(
                poly_system.repr_unify_check(t),
                f"unify failure on random polymorphic system type {t}")

    def test_parser_poly_varsonly(self):
        for i in range(0, 1000):
            self.assertTrue(
                poly_system.repr_unify_check(
                                    poly_system.random_variable_type(5, 0.2)))

    def test_symmetry(self):
        """Ensure that unify is symmetric for variable types."""
        for depth in range (1,5): # this checks at the same depth for t1 and t2, and so can miss things.
            for i in range(0, 500):
                t1 = poly_system.random_variable_type(depth, 0.2)
                t2 = poly_system.random_variable_type(depth, 0.2)
                result = poly_system.unify_sym_check(t1, t2)
                self.assertTrue(result,
                    f"Symmetry check failed: tp('{repr(t1)}'), tp('{repr(t2)}').")
        for depth1 in range (1,2):
            for depth2 in range (1,2):
                for i in range(0, 500):
                    t1 = poly_system.random_variable_type(depth1, 0.2)
                    t2 = poly_system.random_variable_type(depth2, 0.2)
                    result = poly_system.unify_sym_check(t1, t2)
                    self.assertTrue(result,
                        f"Symmetry check failed: tp('{repr(t1)}'), tp('{repr(t2)}').")

    def test_symmetry_general(self):
        for depth1 in range (1,2):
            for depth2 in range (1,2):
                for i in range(0, 500):
                    t1 = poly_system.random_type(depth1, 0.2)
                    t2 = poly_system.random_type(depth2, 0.2)
                    result = poly_system.unify_sym_check(t1, t2)
                    self.assertTrue(result,
                        f"Symmetry check failed: tp('{repr(t1)}'), tp('{repr(t2)}').")

    def test_forall(self):
        for depth1 in range (1,3):
            for depth2 in range (1,4):
                for i in range(0, 500):
                    # from some empirical testing, this seems to get a good mix
                    # of Forall outputs, non-Forall outputs, and non-unifiable
                    # pairs
                    t1 = poly_system.random_variable_type(depth1, 0.2, nonatomics={Forall})
                    t2 = poly_system.random_variable_type(depth2, 0.2)
                    result = poly_system.unify(t1, t2)
                    #  We can't check directly if t2 is a Forall because of
                    # cases like unify(∀Y2, {∀Y3}) = ∀{X}. But t2 should have
                    # been a polymorphic type with no type vars.
                    if result is not None and isinstance(result, Forall):
                        self.assertTrue(t2.is_polymorphic() and len(t2.bound_type_vars()) == 0,
                            f"forall failure: unify({t1}, {t2}) = {result}")

    def test_disjunctive_cases(self):
        def tp(x):
            return poly_system.parse(x, require_exact_type=True)

        self.assertTrue(poly_system.parse_unify_check("[e|t]", "[t|e]"))
        self.assertTrue(poly_system.parse_unify_check("[e|t]", "[t|e]"))
        self.assertTrue(tp("[e|t]") & tp("[t|n]") == tp("t"))
        self.assertTrue(tp("[e|t]") | tp("[t|n]") == tp("[e|t|n]"))
        self.assertTrue((tp("[e|t]") & tp("[<e,t>|n]")) is None)

        with self.assertRaises(TypeParseError): tp("[e|e]")
        with self.assertRaises(TypeParseError): tp("[e]")
        with self.assertRaises(TypeParseError): tp("[e|e")
        with self.assertRaises(TypeParseError): tp("[e|e]]")
        with self.assertRaises(TypeParseError): tp("[X|e]")
        with self.assertRaises(TypeParseError): tp("[e|<e,X>]")

    def test_var_cases(self):
        def tp(x):
            return poly_system.parse(x, require_exact_type=True)

        self.assertTrue(poly_system.parse_unify_check("e", "e"))
        self.assertTrue(poly_system.parse_unify_check("<e,t>", "<e,t>"))
        self.assertTrue(poly_system.parse_unify_check("X", "X"))
        self.assertTrue(poly_system.parse_unify_check("X", "Y"))
        self.assertTrue(poly_system.parse_unify_check("<X,Y>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<X,X>", "<Y,Z>"))
        self.assertTrue(poly_system.parse_unify_check("<<X,X>,X>", "<<e,Y>,Z>"))
        self.assertTrue(poly_system.parse_unify_check(
                                            "<<<e,X>,Y>,Y>", "<<<X,Z>,Z>,e>"))
        self.assertTrue(poly_system.parse_unify_check(
                                "<<X,Y>,<Z,<Z',Z''>>>", "<<X',Y'>,<Y',Z'''>>"))

        self.assertFalse(poly_system.parse_unify_check("e", "t"))
        self.assertFalse(poly_system.parse_unify_check("<e,t>", "<e,e>"))
        self.assertFalse(poly_system.parse_unify_check(
                                            "<<e,X>,X>", "<<Y,Y>,t>"))
        self.assertFalse(poly_system.parse_unify_check(
                                            "<<X,X>,<Y,Y>>", "<<e,Z>,<Z,t>>"))

        # test order consistency in recursive polymorphic unification. When
        # either value could be the principal type under alphabetic variation,
        # unify should always choose the right-hand value (meaning that the
        # lefthand one would need to change). This assumption is relied on by
        # `TypedExpr.try_adjust_type`.
        # (TODO: lots of other things could be tested here...)
        self.assertEqual(poly_system.unify(
                                tp("Y"),
                                tp("X")),
                            tp("X"))
        self.assertEqual(poly_system.unify(
                                tp("<Y,Y>"),
                                tp("<X,X>")),
                            tp("<X,X>"))
        self.assertEqual(poly_system.unify(
                                tp("<Y,<Y,Y>>"),
                                tp("<X,<X,X>>")),
                            tp("<X,<X,X>>"))

        # some complicated occurs check cases discovered via random search
        from lamb.meta import logger
        oldlevel = logger.level
        logger.setLevel(logging.CRITICAL) # suppress occurs check errors
        self.assertTrue(poly_system.unify(
                                tp("<X,<X5,Y5>>"),
                                tp("<X5,X>"))
                        == None)
        self.assertTrue(poly_system.unify(
                                tp("<X5,X>"),
                                tp("<X,<X5,Y5>>"))
                        == None)
        self.assertTrue(poly_system.unify(
                            tp("<X',X''>"),
                            tp("<X'',{(<X',Y''>,{Z'''},Z10)}>"))
                        == None)
        self.assertTrue(poly_system.unify(
                            tp("<X'',{(<X',Y''>,{Z'''},Z10)}>"),
                            tp("<X',X''>"))
                        == None)
        logger.setLevel(oldlevel)

    def test_forall_cases(self):
        def tp(x):
            return poly_system.parse(x, require_exact_type=True)
        def u(x,y):
            return poly_system.unify_sym_check(tp(x), tp(y), require_unify=True)
        self.assertEqual(tp('∀<X,Y>'), tp('∀∀<X,Y>'))
        self.assertEqual(tp('∀<X,Y>'), tp('∀<∀∀X,Y>'))
        self.assertEqual(tp('<e,?>'), tp('<e,∀X>')) # X is implementation-dependent
        self.assertTrue(u('∀X', '∀X'))
        self.assertTrue(u('∀Y', '∀<X,Y>'))
        self.assertEqual(u('∀X', '∀X'), tp('∀X'))
        self.assertEqual(u('∀X', 'X'), tp('X'))
        self.assertEqual(u("<∀X,Y>", "∀<X,Y>"), tp("<∀X,Y>"))
        # assumption here: ?1,?2 are safe from being used as fresh types during
        # this computation. (True on the current implementation)
        self.assertEqual(u('∀X', '?1'), tp('?1'))
        self.assertEqual(u("<?1,?2>", "∀<X,Y>"), tp('<?1,?2>'))
        self.assertEqual(u("<X,Y>", "∀<X,Y>"), tp("<X,Y>"))
        self.assertEqual(u("<X,Y>", "<∀X,∀Y>"), tp("<X,Y>"))
        self.assertEqual(u("<X,Y>", "∀<X,Y>"), tp("<X,Y>"))
        self.assertEqual(u("<X,Y>", "∀<X,X>"), tp("<Y,Y>")) # the Y here is implementation dependent
        self.assertEqual(u("∀<e,X>", "<X,∀Y>"), tp("∀<e,X>"))
        self.assertEqual(u("<e,?1>", "<X,∀Y>"), tp("<e,?1>"))
        self.assertEqual(u('<X2,Z2>','<<Z2,Y2>,∀X>'), tp('<<Z2,Y2>,Z2>'))

        # this unification result can't be represented with an unselective
        # binder while retaining the variable name `Y`
        r = u('<∀X,<Y,∀X>>', '∀<X,<Y,X>>')
        self.assertTrue(len(r.bound_type_vars()) == 2)
        self.assertTrue(r[0].is_fresh())
        self.assertEqual(compact_type_vars(r), tp("<X,<Y,X>>"))

        # can't be represented with unselective binding while capturing
        # (global) identities involving X
        r = u('X', '∀<X,Y>')
        self.assertTrue(len(r.bound_type_vars()) == 2)
        self.assertTrue(r[0].is_fresh() and r[1].is_fresh())

        # similar but for X and Y both
        r = u('X', '<∀X,Y>')
        self.assertTrue(len(r.bound_type_vars()) == 2)
        self.assertTrue(r[0].is_fresh() and not r[1].is_fresh())
        self.assertEqual(r[1], tp('Y'))


