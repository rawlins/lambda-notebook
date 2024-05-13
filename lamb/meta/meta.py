import random
import collections, collections.abc
import contextlib
import IPython.lib.pretty as pretty

import lamb
from lamb import types

from . import core, boolean
from .ply import get_sopt, symbol_is_var_symbol
from .core import is_te, te, global_namespace, get_type_system, Tuple, to_concrete, is_concrete
from lamb import types, parsing, utils
from lamb.utils import ensuremath, dbg_print
from lamb.types import TypeMismatch, type_e, type_t, type_n, BasicType, SetType, TupleType


class DomainError(Exception):
    def __init__(self, element, domain, extra=""):
        self.element = element
        self.domain = domain
        self.extra = extra

    def __str__(self):
        extra = self.extra
        if extra:
            extra = f" ({extra})"
        return f"`{repr(self.element)}`, with domain `{repr(self.domain)}`{extra}"

    def __repr__(self):
        return self.__str__()

    def _repr_markdown_(self):
        return f"<span style=\"color:red\">**{self.__class__.__name__}**</span>: {self.__str__()}"


class OutOfDomain(DomainError):
    def __init__(self, f, a):
        if is_te(f):
            dom = f.type.left.domain
            self.f = f.op
        else:
            dom = f # MetaTerm op or compiled function
            self.f = f
        super().__init__(a, dom)

    def __str__(self):
        return f"`{self.element}` missing from function domain (`{repr(self.f)}`)"


# used primarily for TupleIndex
class MetaIndexError(DomainError):
    def __init__(self, index, indexable, extra=""):
        super().__init__(index, indexable, extra=extra)

    def __str__(self):
        extra = self.extra
        if extra:
            extra = f" ({extra})"
        return f"Invalid index `{repr(self.element)}` for indexable expression `{repr(self.domain)}`{extra}"


class MetaTerm(core.TypedTerm):
    """Term class for storing direct references to underlying objects in a type domain."""
    def __init__(self, name, typ=None, setfun=False, copying=False, **kwargs):
        type_verified = False
        if isinstance(name, MetaTerm):
            # essentially, copy `name`
            if typ is None:
                typ = name.type
                copying = True
            name = name.op

        # though super sets this, for various error cases on the type check it
        # is useful to set it in advance and then rely on it in the type check
        self.op = name
        self.type = None

        if not copying:
            typ = self.check_type_domain(typ=typ, setfun=setfun)

        # this is kind of clunky, but enforce various normalized representations
        # from the type domain. E.g. this puts a `_` on atomic string values,
        # wraps dicts/sets with frozendict/frozenset
        # XX normalization is already happening during the type check, can it
        # be reused?
        name = typ.domain.normalize(name)

        super().__init__(name, typ=typ, copying=True, validate_name=False)
        self._variable = False
        self._constant = True

        # cosmetics: hide the type subscript in rich reprs for t/n
        if self.type == type_t or self.type == type_n:
            self.suppress_type = True

        # not set by superclass with copying=True
        self.set_type_env(self.calc_type_env())
        self.assignment_name = None

    def check_type_domain(self, typ=None, setfun=False):
        if typ is None:
            # try to infer the type from self.op
            typ = core.get_type_system().get_element_type(self.op, setfun=setfun)
            if typ is None:
                raise parsing.ParseError(
                            f"Unknown type domain element: `{self.op_repr()}`")
            return typ
        else:
            if self.op not in typ.domain:
                if typ.is_polymorphic():
                    # it's helpful to have a specific error for this case
                    raise TypeMismatch(self.op, typ,
                        error=f"Can't instantiate domain elements with polymorphic types")
                else:
                    raise TypeMismatch(self.op, typ,
                        error=f"Invalid element reference for type domain of `{typ}` in term: `{self.op_repr()}`")
            if isinstance(typ, types.DisjunctiveType):
                # always fully resolve a disjunctive type if it is provided to
                # this function
                dtyp = typ.resolve_element_type(self.op)
                if dtyp is None:
                    # shouldn't be possible...
                    raise TypeMismatch(self.op, typ,
                        error="failed to fully resolve disjunctive type in MetaTerm??")
                typ = dtyp
            # XX it might be possible to handle a type variable here by
            # resolving it as in the `None` case?
            return typ

    def _recheck_domain(self):
        if self.op not in self.type.domain:
            raise DomainError(self.op, self.type.domain)

    def _compile(self):
        # caveat: functional types return as their underlying python
        # implementation. ApplicationExpr._compile will handle this, but other
        # users will need special casing.
        def c(context):
            # XX can this domain check be handled elsewhere?
            self._recheck_domain()
            return self.op
        return c

    def simplify(self, **sopts):
        # if we are doing an evaluate pass, recheck the domain. This is to
        # validate expressions that were generated out of the scope of a
        # domain restriction, relative to one.
        # currently: only do this for atomic types.
        if get_sopt('evaluate', sopts) and len(self.type) == 0:
            self._recheck_domain()
        return self

    @classmethod
    def _apply_impl(cls, fun, arg):
        if isinstance(fun, collections.abc.Set):
            return arg in fun
        elif isinstance(fun, collections.abc.Mapping):
            # XX is there a better way to handle this?
            if arg in fun:
                return fun[arg]
            else:
                raise OutOfDomain(fun, arg)
        elif callable(fun):
            return fun(arg)
        else:
            raise ValueError(f"Unknown callable object `{fun}`!")

    def set(self):
        if not isinstance(self.type, types.SetType):
            raise TypeError(f"Can't convert MetaTerm of type {repr(self.type)} to a set")
        return frozenset({MetaTerm(elem, typ=self.type.content_type) for elem in self.op})

    def tuple(self):
        if not isinstance(self.type, types.TupleType):
            raise TypeError(f"Can't convert MetaTerm of type {repr(self.type)} to a tuple")
        return tuple(MetaTerm(self.op[i], typ=self.type[i]) for i in range(len(self.op)))

    def apply(self, arg):
        if not self.type.functional() or not core.get_type_system().eq_check(self.type.left, arg.type):
            raise TypeMismatch(self, arg, error="Function-argument application: mismatched argument type to MetaTerm")

        # n-ary application will supply a Tuple here
        if is_concrete(arg):
            # XX demeta?
            arg = MetaTerm(to_concrete(arg))
        elif not arg.meta():
            return self(arg)

        if isinstance(self.op, collections.abc.Set):
            # XX why does this have to be disjunctive?? It makes this code very
            # messy
            # this will raise if somehow self.type.right is not t
            return MetaTerm(self._apply_impl(self.op, arg) or self._apply_impl(self.op, arg.op),
                typ=self.type.right)
        elif isinstance(self.op, collections.abc.Mapping):
            # XX why does this have to be disjunctive??
            try:
                return MetaTerm(self._apply_impl(self.op, arg), typ=self.type.right)
            except OutOfDomain:
                pass
            return MetaTerm(self._apply_impl(self.op, arg.op), typ=self.type.right)
        else:
            return self._apply_impl(self.op, arg)

    def meta(self):
        return True

    def copy(self):
        return self.copy_local()

    def copy_local(self, **kwargs):
        r = self.copy_core(MetaTerm(self.op, typ=self.type))
        r.latex_op_str = self.latex_op_str
        r.assignment_name = self.assignment_name
        return r

    def under_assignment(self, assignment, **kwargs):
        # ensure that these terms are completely inert to assignments
        return self

    def __bool__(self):
        # TODO: currently `0` converts to False, but perhaps it shouldn't,
        # given that it doesn't compare equal to False, and MetaTerm(0, type_t)
        # gives a TypeMismatch.
        return bool(self.op)

    def __eq__(self, other):
        if other in self.type.domain:
            # compare as equal to domain elements.
            # while this will generally behave symmetrically if the type domain
            # is constructed from python basic types, symmetric behavior can't
            # be assumed in general. If the type domain involves objects that
            # implement __eq__, and you want symmetry, you will have to special
            # case the comparison to a MetaTerm.
            return self.op == other
        elif isinstance(other, core.TypedExpr):
            # note: without the type check, 0 vs False and 1 vs True compare equal,
            # because `bool` is a subtype of `int`
            return other.meta() and self.type == other.type and self.op == other.op
        else:
            # neither a TypedExpr no a python object in the type domain
            return False

    def __hash__(self):
        # overrode __eq__, so also need to override __hash__. We hash with
        # the operator, since dict comparison relies on this.
        if self.op.__hash__:
            return self.op.__hash__()
        else:
            return hash(self.op)

    def op_repr(self, rich=False, sf=False, use_renames=True):
        if self.type is None:
            # error in constructor, just need something here
            return str(self.op)
        sup = ""
        if rich and use_renames:
            sup = self.type.domain.element_repr(self.op, rich=rich, use_renames=False)
        r = self.type.domain.element_repr(self.op, rich=rich, use_renames=use_renames)
        if rich:
            old = r
            if sf:
                r = f"\\textsf{{{r}}}"
            if sup and sup != old:
                r = f"{{{r}}}^{{\\textsf{{{sup}}}}}"
        return r

    def calc_type_env(self, recalculate=False):
        # currently, MetaTerms are not represented at all in the type
        # environment. They definitely need to be absent from term_mapping, but
        # should they be present in some form?
        return core.TypeEnv()

    def type_env(self, constants=False, target=None, free_only=True):
        return set()

    def free_terms(self, var_only=False):
        return set()

    def __repr__(self):
        return self.op_repr(use_renames=False)

    def _repr_pretty_(self, p, cycle):
        if cycle:
            p.text("MetaTerm(...)")
        else:
            use_renames = not getattr(p, '_define_context', True)
            p.text(self.op_repr(use_renames=use_renames))

    def latex_str(self, show_types=True, assignment=None, use_renames=None, **kwargs):
        # TODO: similar to __repr__, possibly this code should be on the
        # type domain itself
        # if just using `op` as the name, we use textsf, but setting
        # an arbitrary latex name is allowed
        if use_renames is None:
            use_renames = True
        elem_renamed = (self.type is not None
                        and self.type.domain.element_rename(self.op))
        if self.latex_op_str is None:
            if use_renames and self.assignment_name is not None and not elem_renamed:
                # XX this is a bit ad hoc, could it be better systematized?
                # maybe a piece of the assignment itself should be saved?
                # should domain element renames also be shown as a superscript?
                if isinstance(self.assignment_name, tuple):
                    aname, aname2 = self.assignment_name
                else:
                    aname = self.assignment_name
                    aname2 = None
                if isinstance(self.type, types.BasicType):
                    superscript = self.op_repr(rich=True, sf=True)
                else:
                    # don't try to show the actual value for this case
                    superscript = "\\text{\\textsf{[meta]}}"
                if aname2:
                    # assumption: aname2 is a str
                    superscript = f"{aname2}/{superscript}"
                return aname.latex_str(show_types=show_types,
                                            assignment=assignment,
                                            superscript=superscript,
                                            sf=not symbol_is_var_symbol(aname.op),
                                            **kwargs)
            else:
                # render a domain element name as sans serif
                op_str = self.op_repr(rich=True, sf=True, use_renames=use_renames)
        else:
            # assumption: this is only used in cases where the op string is
            # giving an extremely stable constant name (e.g. \bot for False)
            op_str = f"{self.latex_op_str}"
        if not show_types or not self.should_show_type(assignment=assignment):
            return ensuremath(op_str)
        else:
            # does this need to be in a \text? frontend compat in general...
            return ensuremath(f"{op_str}_{{{self.type.latex_str()}}}")

    def _repr_latex_(self):
        # override: when directly inspecting an arbitrary MetaTerm, suppress
        # any assignment-derived name, except for the BasicType case, which
        # always shows the value
        return self.latex_str(suppress_parens=True, use_renames=isinstance(self.type, BasicType))

    @classmethod
    def random(cls, random_ctrl_fun, typ=None, blockset=None, usedset=None,
                            prob_used=0.8, prob_var=0.5, max_type_depth=1):
        # MetaTerm can also be instantiated by TypedTerm.random, and that is
        # the only way that is reachable recursively
        if typ is None:
            typ = random.choice(list(core.get_type_system().atomics))

        if typ not in core.get_type_system().atomics:
            raise TypeMismatch(typ, "Can't randomly instantiate MetaTerm at this type")

        return core.TypedExpr.term_factory(typ.domain.random(), typ)


###################
# wrappers for TypedExpr compilation


def compile_term_check(te, context=None):
    if not is_te(te):
        return None # can't verify the context
    if context is None:
        context = {}
    missing_terms = [k for k in te.free_terms() if k not in context]
    if missing_terms:
        # without an explicit check, piecemeal KeyErrors get produced
        # XX could trigger this message *on* a KeyError?
        missing_terms.sort()
        missing_terms = ", ".join([repr(core.TypedTerm(k, typ=te.get_type_env().term_type(k)))
                                        for k in missing_terms])
        raise TypeError(f"Context for executing `{repr(te)}` is missing free term(s): {missing_terms}")
    return True


def compiled(e, recompile=False, with_context=None, validate=False):
    """Given some TypedExpr `e`, produce a compiled version of `e` suitable
    for direct execution. If `e` is not a TypedExpr, this returns `e`, and
    for this case none of the parameters have an effect. This can be used as
    a safer version of accessing e._compiled, because it can be
    used idempotently (e.g. ``compiled(compiled(e)) == compiled(e)``).

    Parameters
    ----------
    e: Any
        a potential TypedExpr to compile
    recompile: bool, optional
        if `True`, prevents compilation from using a cached version.
    with_context: Mapping, optional
        if provided, immediately call a compiled TypedExpr with this parameter
        used as the context. If `None` (the default), don't call.
    validate: bool, optional
        if True, validate `e` before compiling against the context, checking
        to ensure that all free terms are supplied. Note that even if
        `with_context` is set to `None`, setting `validate` to `True` will
        force validation. A `None` context in this case is equivalent to the
        empty mapping.

    Returns
    -------
    Any
        A compiled TypedExpr, with or without a context supplied, or `e` if `e`
        is not a TypedExpr.
    """
    if is_te(e):
        if recompile:
            e._reset_compiled()
        if validate:
            compile_term_check(e, with_context)
        if with_context is not None:
            return e._compiled(with_context)
        else:
            # defer context
            return e._compiled
    else:
        # XX is it possible to try supplying context here?
        return e


def _do_dynamic_tcheck(fun, typ, args, arity_only=False):
    """Do some minimal dynamic type-checking for a function at a type, given
    some args. If `arity_only` is set, just check arity against `typ`, also
    handling the case where typ.left is a tuple. If `arity_only` is True, we
    also check each argument against the type's domain.

    If this does a full type check, it will normalize elements of `args` to
    the relevant type domain by side effect!

    This check is potentially costly when arguments are not simple, partly
    because of this normalization. For example, sets/dicts will be converted
    to their frozen variants to ensure hashability.
    """
    if not typ.functional() and args:
        raise TypeError(f"Argument supplied to non-functional wrapped expression {fun.__qualname__}")
    if not isinstance(typ, types.FunType):
        return True # XX handle
    if typ.left.is_polymorphic():
        return True
    if isinstance(typ.left, types.TupleType):
        arity = len(typ.left)
        argtype = typ.left
    else:
        arity = 1
        argtype = (typ.left,)
    if arity != len(args):
        # XX this error is hard to word clearly in the context of both curried
        # and uncurried functions
        raise TypeError(f"Arity mismatch: {len(args)} arguments supplied directly to arity {arity} wrapped expression {fun.__qualname__}")
    # the domain check is potentially costly
    if not arity_only:
        for i in range(len(argtype)):
            if args[i] not in argtype[i].domain:
                raise TypeError(f"{fun.__qualname__} received mismatched argument for type {argtype[i]}: `{repr(args[i])}`")
            # side effect warning!
            args[i] = argtype[i].domain.normalize(args[i])
    return True


def wrap_compiled(te, _typ=None, _check_domain=True, _mirror=False, **context):
    """Wrap a compiled ``TypedExpr`` with a single (potentially tuple/n-ary)
    argument so that it can be more easily called in Python code. This is a
    relatively low-level version of this idea, and so unless you know what
    you're doing, it is better to use `exec` or `to_callable`. (The latter is
    implemented by repeatedly calling `wrap_compiled`.)

    Parameters
    ----------
    te: Any
        A ``TypedExpr`` to be compiled, or an already compiled and executed
        ``TypedExpr``. (I.e., if it's already compiled, it should have its context
        already supplied as well.)
    _typ: lamb.types.TypeConstructor, optional
        An explicit type for `te`, used only if `te` is precompiled. If `te`
        is not precompiled, the type will be taken directly from `te`,
        overriding this parameter. This is used simply for arity checking, so
        that the return will produce an error if the compiled version is not
        expecting an argument and it gets one, and not take an argument if
        it should not.
    _check_domain: bool
        If ``True``, the wrapped function will check its arguments against the
        type domain for the input type (if type is available). This is a
        potentially costly check, but makes it a lot easier to spot common
        mistakes. This check handles *only* concrete types; in particular,
        polymorphic input types are not checked at all.
    **context:
        A sequence of named parameters to use as the context for calling the
        compiled version of `te`. Ignored of `te` is pre-compiled.

    Returns
    -------
    Any
        This has two cases. In both cases, `context` is supplied while building
        the wrapped function, so it must be complete for all free terms.

        * If `te` has a functional type (or is a pre-compiled callable): return
          a callable that checks arity, before calling compiled `te` with that
          argument. The argument to this callable is assumed to be already
          compiled with a context supplied.
        * If `te` is not functional/callable: return the compiled and called
          value of `te`.

    See also
    --------
    `to_callable`, `exec`: probably the functions you want to call directly.
    """
    in_context = compiled(te, with_context=context)
    if is_te(te):
        qualname = te._compiled.__qualname__
        _typ = te.type
    else:
        qualname = in_context.__qualname__
    if (_typ is not None and not isinstance(_typ, types.FunType)
                or not is_te(in_context) and not callable(in_context)):
        # XX should this check use type?
        return in_context
    if is_te(te):
        repr_for_err = repr(te)
    else:
        # if te is a wrapped function, the qualname will provide details, but
        # otherwise, it should at least provide a function name?
        repr_for_err = qualname
    def wrapped_fun(*args):
        args = tuple(compiled(a, with_context=context) for a in args)
        if _typ is not None:
            args = list(args)
            _do_dynamic_tcheck(in_context, _typ, args, arity_only=not _check_domain)
        if len(args) == 0:
            # len 0 just returns the compiled and executed te.
            # XX this case is a bit weird?
            return in_context
        if len(args) == 1:
            return in_context(args[0])
        return in_context(args)
    wrapped_fun.__qualname__ = f"wrap_compiled({qualname})"
    return wrapped_fun


def to_callable(te, _uncurry=False, _allow_partial=False, _check_domain=True, **context):
    """Wrap an n-ary, possibly curried, function so that it can be called
    from python. This is lower-level than `exec`.

    Parameters
    ----------
    te: lamb.meta.TypedExpr
        A ``TypedExpr`` to be compiled and called
    _uncurry: bool, optional
        If ``True``, and `te` is a curried n-place function, the returned
        callable will take the arguments in an un-curried (n-ary) way.
    _allow_partial: bool, optional
        When uncurrying, if set to ``True``, this will not require that all
        arguments be supplied in the n-ary sequence. That is, it'll allow
        underapplication. The result of under-application *will* be curried.
        If some argument places already take tuples, this will not be flattened.
    _check_domain: bool
        If ``True``, the wrapped function will check its arguments against the
        type domain for the input type (if type is available). This is a
        potentially costly check, but makes it a lot easier to spot common
        mistakes. This check handles *only* concrete types; in particular,
        polymorphic input types are not checked at all.
    **context: dict, optional
        The context to interpret `te` in.

    Returns
    -------
    Any
        This function has two cases.

        * If `te` is functional, this function will return a callable that
          calls compiled `te` with arguments supplied (either in a curried or
          uncurried fashion as determined by the parameters). The result fully
          checks arity.
        * If `te` is not functional, return the compiled and called instance of
          `te`.

    See also
    --------
    `exec`: the most general wrapper for compiled metalanguage code.
    """
    typ = te.type
    arg_slots = []
    repr_for_err = repr(te)
    wrapped = te
    te_qualname = None
    if isinstance(typ, types.FunType):
        arg_slots.append(typ.left) # XX could extract argument name
        wrapped = wrap_compiled(wrapped, _typ=typ, _check_domain=_check_domain, **context)
        te_qualname = wrapped.__qualname__
        typ = typ.right
        # XX handle and/or prevent polymorphism, disjunction, ...?

        # subsequent wrappings need to invert application order (XX messy)
        # we implement things this way in order to correctly handle variable
        # capture for `wrapped`/`typ` in the loop
        def build_rewrapped(_wrapped, _typ):
            f = lambda x: wrap_compiled(_wrapped(x), _typ=_typ, _check_domain=_check_domain, **context)
            f.__qualname__ = _wrapped.__qualname__
            return f

        while isinstance(typ, types.FunType):
            arg_slots.append(typ.left)
            wrapped = build_rewrapped(wrapped, typ)
            typ = typ.right
    else:
        wrapped = wrap_compiled(wrapped, _typ=typ, _check_domain=_check_domain, **context)

    if _uncurry and arg_slots:
        def uncurried(*args):
            # overrides the arity checks from wrap_compiled
            if len(args) > len(arg_slots):
                raise TypeError(
                    f"Too many arguments ({len(args)} > {len(arg_slots)}) supplied for compiled function {repr_for_err}")
            if not _allow_partial and len(args) != len(arg_slots):
                raise TypeError(
                    f"Too few arguments ({len(args)} < {len(arg_slots)}) supplied for compiled function {repr_for_err}")
            call = wrapped
            for a in args:
                # the curried wrapper handles both compilation of `a` and
                # supplying `context`
                call  = call(a)
            return call
        if te_qualname:
            # using this qualname with an inner function is a bit weird, but
            # it gets the idea across at least
            uncurried.__qualname__ = f"uncurried({te_qualname})"
        return uncurried
    else:
        return wrapped


def exec(te, *args,
    _typecheck=True, _uncurry=False, _allow_partial=False, _check_domain=True,
    **context):
    """Execute `te` by compiling it, supplying a context, and potentially some
    arguments if `te` is a function. Any unsupplied arguments will be
    "deferred": the return will be a callable that can then take those
    arguments.

    Parameters
    ----------
    te : lamb.meta.TypedExpr
        A TypedExpr to execute.
    *args: List[lamb.meta.TypedExpr], optional
        A sequence of arguments to compile and supply to `te` when executing it.
        This does not need to exhaust the arguments for `te`, and if argument
        places are left out of `args`, they will be deferred (i.e. the return
        will be a callable).
    _typecheck: bool, optional
        If ``True``, statically type-check `args` using metalanguage type
        inference. This *only* applies to arguments supplied to `exec`, and
        not deferred arguments for `te`. (See also: `_domain_check`.)
    _uncurry: bool, optional
        If ``True``, and the return would be a callable, uncurry any arguments
        to functions so that the return expects them in an n-ary way.
    _allow_partial: bool, optional
        If ``True``, and uncurrying happens, allow underapplication. (The result
        of underapplication will be a curried function.)
    _domain_check: bool, optional
        If ``True``, any deferred arguments will be dynamically type-checked
        by the wrapped function; see the same named parameter in
        ``to_callable``.
    **context: dict, optional
        A context parameter for executing all TypedExprs; this must supply
        values for any free terms in `te`. Unlike other wrapper functions,
        `exec` does not assume that context values are compiled, and will
        compile them if need. If they are compiled, they are executed with an
        empty context, so this is not suitable if they themselves contain free
        terms. This does accept pre-compiled/executed values. `exec` will raise
        ``TypeError`` if free terms are missing from `context`. However, it is
        important to keep in mind that no type checking is done when executing
        something given `context`.

    Returns
    -------
    Any
        A potentially callable compiled and executed (using `context`) version
        of `te`. It will be callable just in case `te` is functional and the
        supplied `args` leave some argument places unfilled.
    """
    # this shadows `exec`, but if `exec` is ever run in this module, something
    # has gone very wrong
    if _typecheck and args:
        # type check by building a TypedExpr with any supplied args. Can be
        # costly compared to deferring them.
        for a in args:
            te = te(a)
        # XX should this call reduce_all(), or even simplification? In some
        # extremely limited empirical testing, reduce_all is slower...
        args = []

    # do some validation that lower-level wrappers don't do
    # note that no type checking of any sort is done on `context` aside from
    # this. This requires any contextual TypedExprs to themselves have no
    # context requirements...
    # XX could lift certain things to MetaTerms?
    compile_term_check(te, context)
    context = {k: compiled(context[k], validate=True, with_context={}) for k in context}

    r = to_callable(te,
        _uncurry=_uncurry, _allow_partial=_allow_partial, _check_domain=_check_domain,
        **context)
    # n.b. the parameters to `to_callable` have no effect if there are no
    # remaining argument slots at this point.
    if args:
        args = [compiled(a, with_context=context) for a in args]
        # if any args remain to apply, apply them
        if _uncurry:
            r = r(*args)
        else:
            # overapplication check here?
            for a in args:
                r = r(a)
    return r


def is_propositional(e):
    # in principle, could allow type variables here
    return e.type == types.type_t

# TODO: run these with time-based timeouts, rather than heuristic maxes
# TODO: there might be faster ways to do this with numpy arrays + broadcasting

def combinations_gen(l, elems):
    for c in itertools.product(elems, repeat=len(l)):
        yield dict(zip(l, c))

# the following code is essentially calculating
# `list(combinations_gen(terms, elems))`. Unfortunately, doing this the compact
# way is noticeably inefficient. In fact, unfortunately, I haven't
# even been able to get a generator version that is as fast as the following
# code (I guess because of yield overhead?)
#
# >>> s = list('abcdefghijklmnopqrstuv')
# >>> %time x = combos(s, (False, True), max_length=100)
# >>> %time x = list(combinations_gen(s, (False, True)))
# CPU times: user 1.04 s, sys: 282 ms, total: 1.32 s
# Wall time: 1.33 s
# CPU times: user 3.65 s, sys: 242 ms, total: 3.89 s
# Wall time: 3.97 s

# warning, exponential in both time and space in the size of `terms`...
def combinations(terms, elems, max_length=20):
    # 20 here is somewhat arbitrary: it's about where exponential blowup gets
    # noticeable on a reasonably fast computer with two elems
    # XX should factor in elems
    if len(terms) > max_length:
        raise ValueError(f"Tried to calculate combinations for an overlong sequence: {repr(terms)}")
    if not elems:
        raise ValueError("Can't produce value combinations without elements")
    if not terms:
        return [{}]
    if len(elems) == 1:
        # this case is very simple, return early
        return {t: elems[0] for t in terms}
    stop = len(terms) - 1
    elem_range = range(len(elems) - 2)
    # now we can assume 2+ elems
    last_elem = elems[-1]
    last2_elem = elems[-2]
    g = []
    def combos_r(i, accum):
        if elem_range:
            for j in elem_range:
                branch = accum.copy()
                branch[terms[i]] = elems[j]
                if i < stop:
                    combos_r(i + 1, branch)
                else:
                    g.append(branch)
        # unroll two iterations. Doing this gets a non-trivial speedup for
        # large term lists, partly from the unrolling, partly from not copying
        # for the last accum, and partly from the precalculation of the element
        # values rather than accessing from elems. Doing this is essentialy an
        # optimization for the boolean case.
        branch = accum.copy()
        branch[terms[i]] = last2_elem
        accum[terms[i]] = last_elem
        if i < stop:
            combos_r(i + 1, branch)
            combos_r(i + 1, accum)
        else:
            g.append(branch)
            g.append(accum)

    combos_r(0, dict())
    return g


def all_boolean_combos(l, cur=None, max_length=20):
    return combinations(l, (False, True), max_length=max_length)


def truthtable_repr(t):
    # this is maybe a bit misleading to use, since `0` and `1` in the
    # metalanguage are not convertable to False/True. But I find these
    # the most readable symbols to use in a truth-table.
    if t == False:
        return 0
    if t == True:
        return 1
    try:
        return t._repr_latex_()
    except AttributeError:
        return t


class Evaluations(collections.abc.Sequence):
    def __init__(self, expression, assignments=None, display_assignment={}):
        if assignments is None:
            assignments = []
        self.display_assignment = display_assignment

        self.expression = expression
        env = expression.get_type_env()
        self.terms = env.terms(sort=True)
        # slightly weird, but we need to reconstruct the terms for display
        # purposes, and all we have right now is strings
        self.term_exprs = [core.term(t, typ=env.term_type(t)) for t in self.terms]
        self.update_evals(assignments)

    def update_evals(self, assignments):
        # XX use `exec` if we can
        self.evaluations = [
            (v, self.expression.under_assignment(v).simplify_all())
            for v in assignments]
        in_use = set().union(*[v.keys() for v in assignments])
        # store this as a mask on self.terms
        self.in_use = [t in in_use for t in self.terms]
    
    def __len__(self):
        return len(self.evaluations)

    def __getitem__(self, i):
        """Return a pair consisting of a valuation and the evaluation of
        the stored expression under that valuation."""
        return self.evaluations[i]

    def __eq__(self, other):
        """Return True if self and other have exactly the same set of
        evaluations. This requires syntactic term identity for the evaluated
        terms, but does not require the two expressions to be identical. For
        a completely valued expression, this therefore provides a form of
        semantic equivalence."""

        # relies on evaluations having the same sort in self and other...
        return self.evaluations == other.evaluations

    def get_valued_terms(self, expr=False):
        if expr:
            l = [e.under_assignment(self.display_assignment)
                                                    for e in self.term_exprs]
        else:
            l = self.terms
        return [t[0] for t in zip(l, self.in_use) if t[1]]
    
    def _repr_markdown_(self):
        header = ([f"| {t._repr_latex_()} " for t in self.get_valued_terms(expr=True)]
                  + [f"| {self.expression.under_assignment(self.display_assignment)._repr_latex_()}"])
        sep = ["| :---:" for col in header]
        rows = []
        
        def tname(v, t):
            if t in v:
                return truthtable_repr(v[t])
            else:
                return ""

        for row in self:
            v, result = row
            rows.append(
                [f"| {tname(v, t)}" for t in self.get_valued_terms()]
                + [f"| {truthtable_repr(result)}"])

        return ("".join(header) + "|\n"
                + "".join(sep) + "|\n"
                + "".join(["".join(row) + "|\n" for row in rows]))


def truthtable_valuations(e, max_terms=12):
    """Calculate all possible valuations for type `t` terms in `e`. No other
    terms are valued."""
    env = e.get_type_env()
    terms = [t for t in env.terms(sort=True) if env.term_type(t) == types.type_t]
    # 12 here is once again just chosen as a default heuristic
    if len(terms) > max_terms:
        raise ValueError(f"Tried to calculate truthtable for an overlong sequence: {repr(e)}")
    return all_boolean_combos(terms)


def extract_boolean(*exprs):
    """Extract a pure boolean skeleton from all expressions in `exprs`,
    together with a mapping that will convert these skeletons back into
    their original forms.
    
    Note that all variables used in more than one formula must have compatible
    types, and as needed any type variables shared across expressions may be
    resolved to their principal types. Consequently, if type variables are in
    play, the resulting mapping may not recover exactly the starting
    expressions.
    
    All input expressions must be exactly type t."""

    for e in exprs:
        if not is_propositional(e):
            raise ValueError(f"Can't extract boolean frame from non-boolean `{repr(e)}`")
    mappings = {}
    mapped = {}
    env = core.TypeEnv()
    # ensure the types are actually mergeable...
    for e in exprs:
        env.merge(e.get_type_env())
    used_vars = set(env.terms())
    i = 0

    def fresh():
        nonlocal i
        i += 1
        name = f"p{i}"
        if name in used_vars:
            return fresh()
        return core.term(name, typ=types.type_t)

    def extract_boolean_r(e):
        nonlocal mappings
        e = e.under_type_assignment(env.type_mapping)
        if e.atomic():
            return e.copy()
        elif e.__class__ in boolean.pure_ops:
            return e.copy_local(*[extract_boolean_r(subexpr) for subexpr in e])
        elif e in mapped:
            # note: syntactic equivalence only!
            return mapped[e]
        else:
            var = fresh()
            mappings[var.op] = e
            mapped[e] = var
            return var
    results = [extract_boolean_r(e.under_type_assignment(env.type_mapping))
                                                                for e in exprs]
    return (results, mappings)


def truthtable(e, max_terms=12, simplify=False, extract=False):
    """
    Calculate a truth-table for expression `e`. If `e` is a purely boolean
    expression (see `is_pure`) this will be a complete truth-table, but
    otherwise it may have unreduced expressions in the result.
    
    This is a brute-force calculation, and so is exponential (time and space)
    in the number of terms, hence the heuristic `max_terms` parameter.
    """
    if simplify:
        e = e.simplify_all(reduce=True)
    a = {}
    if extract:
        e, a = extract_boolean(e)
        e = e[0]
    return Evaluations(e, truthtable_valuations(e, max_terms=max_terms),
                    display_assignment=a)


def truthtable_equiv(e1, e2, simplify=True):
    """Are e1 and e2 equivalent in terms of evaluation on a truth-table?

    e1 and e2 must be propositional. This supports formulas with complex
    propositional elements, but they will be compared on syntactic equivalence
    only."""

    return truthtable_valid(e1.equivalent_to(e2), simplify=simplify)


def truthtable_valid(e, simplify=True):
    if simplify:
        e = e.simplify_all(reduce=True)
    result, assignment = extract_boolean(e)
    # display(truthtable(result[0]))
    return all((eval[1] == True) for eval in truthtable(result[0]))


def truthtable_contradictory(e, simplify=True):
    if simplify:
        e = e.simplify_all(reduce=True)
    result, assignment = extract_boolean(e)
    return all((eval[1] == False) for eval in truthtable(result[0]))


def ensure_te_vals(m):
    # caveat: this changes m!
    for k in m:
        if not is_te(m[k]):
            m[k] = te(m[k])
    return m


class Assignment(utils.Namespace):
    """This class represents an assignment function that can be incrementally
    modified.  Like the parent class `utils.Namespace`, it uses a ChainMap for
    most of the implementation details. All values are required to be
    `meta.core.TypedExpr` objects."""
    def __init__(self, _base=None, _name=None, **kwargs):
        """Instantiate an `Assignment`.

        Parameters
        ----------
        _base : collections.abc.Mapping, optional
            a map to initialize with. Values must be `TypedExpr`.
        _name : str, optional
            a (mostly cosmetic) name for the asignment, treated as empty if
            not provided.
        **kwargs : dict, optional
            key-value pairs to initialize with. Values must be `TypedExpr`.
        """
        if _base is None:
            _base = dict()
        else:
            _base = ensure_te_vals(_base.copy())

        super().__init__(_base)
        self.update(**kwargs)

        if _name is None:
            self.name = ""
        else:
            self.name = _name

    def copy(self):
        return Assignment(_name=self.name, _base=self.items.copy())

    def __setitem__(self, key, value):
        """Set a value in the mapping. `value` must be a `meta.core.TypedExpr`."""
        if not is_te(value):
            value = te(value)
        super().__setitem__(key, value)

    def update(self, m=None, /, **kwargs):
        """Update the mapping in place. All values must be instances of
        `meta.core.TypedExpr`."""
        kwargs = ensure_te_vals(kwargs)
        if m is not None:
            m = ensure_te_vals(m.copy())
            self.items.update(m, **kwargs)
        else:
            self.items.update(**kwargs)

    def modify(self, m=None, /, **kwargs):
        """Modify `self` by creating a new element in the underlying mapping
        chain, and updating with `m` and `**kwargs`. All values must be
        instances of `meta.core.TypedExpr`.

        Parameters
        ----------
        m : collections.abc.Mapping, optional
            A mapping to update with. Values must be `TypedExpr`.
        **kwargs : dict, optional
            Key-value pairs to update with. Values must be `TypedExpr`.
        """
        super().modify() # add a new child to self.items
        self.update(m, **kwargs)

    # new_child, pop_child, shift implementation via super

    def merge(self, m=None, /, **kwargs):
        """Merge in another assignment, requiring type-consistency of any
        modifications to existing mappings. The update will happen at the
        principal type. This inserts a new mapping into the chain before
        updating, so update history is stored.

        This has non-symmetric behavior: if the types are ok, and the value here
        is a term, the value in `assignment` (at the principal type) will
        override the value in self. (The previous value's type will not be
        adjusted.)

        Parameters
        ----------
        m : collections.abc.Mapping, optional
            A mapping to merge. Values must be `TypedExpr`.
        **kwargs : dict, optional
            Key-value pairs to merge. Values must be `TypedExpr`.
        """

        m = self.new_child(m, **kwargs)
        for k in m:
            if k in self:
                # this will raise a TypeMismatch if the merge fails. `m`
                # is in an intermediate state, but that doesn't affect `self`.
                m[k] = core.merge_tes(self[k], m[k], symmetric=False)

        return m

    def _update_text(self, m, rich=False, linearized=True, **kwargs):
        # text for a single mapping's worth of updates
        if rich and not linearized:
            return utils.dict_latex_repr(m, linearized=False, **kwargs)
        elif rich:
            # use Heim & Kratzer style reverse notation
            a_strs = [f"{m[k].latex_str(**kwargs)}/{k}" for k in m]
        else:
            a_strs = [f"{repr(m[k])}/{k}" for k in m]
        return f"[{','.join(a_strs)}]"

    def text(self, rich=False, linearized=True, **kwargs):
        maps = self.maps[::-1] # reverse it
        if self.name:
            r = self.name
        elif len(maps):
            # only linearize non-superscripted updates
            r = self._update_text(maps[0], rich=rich, linearized=linearized, **kwargs)
            maps = maps[1:]
        else:
            r = "[]" # anything else?

        for i in range(len(maps)):
            i_text = self._update_text(maps[i], rich=rich, **kwargs)
            if rich:
                # the superscripting is the Heim & Kratzer style, but I'm not
                # sure I really like it...
                r = ensuremath(f"{{{r}}}^{{{i_text}}}")
            else:
                r = f"{r}{i_text}"
        return r

    @contextlib.contextmanager
    def under(self, force_names=False):
        """Temporarily apply all definitions in this assignment to the global
        namespace. This also update the type system's basic type element names
        with any relevant definitions in `self` so that they are rendered
        using their assignment names. Modifying the global namespace in the
        scope of this call will change this assignment! (This behavior can be
        avoided by copying first.)

        Parameters
        ----------
        force_names: bool, default: False
            if `True`, this will overwrite any existing domain element renames,
            and also use the last rename in `self` rather than the first in
            cases of duplicates.

        Yields
        ------
        AttrWrapper
            A wrapped version of `self` (in contrast to the superclass, not
            of the global namespace!)
        """

        nameable = {k: self[k] for k in self if self[k].meta()
                                and not symbol_is_var_symbol(k)
                                and isinstance(self[k].type, types.BasicType)}
        n_types = {nameable[k].type for k in nameable}
        with contextlib.ExitStack() as stack:
            for typ in n_types:
                by_type = {k: nameable[k] for k in nameable if nameable[k].type == typ}
                stack.enter_context(typ.with_names(by_type, force=force_names))
            # note: changes to the global namespace in the scope of this call
            # will change the assignment!
            stack.enter_context(super().under())
            # n.b. unlike super().under(), only yield an object that includes
            # the *current* assignment
            yield utils.AttrWrapper(self)

    def _repr_latex_(self):
        return self.latex_str()

    def _repr_markdown_(self):
        return None

    def latex_str(self, linearized=False, **kwargs):
        return ensuremath(self.text(rich=True, linearized=linearized, **kwargs))


class Model(collections.abc.MutableMapping):
    """A complex mapping object that represents both an assignment and a set of
    domain restrictions for type domains; for the purpose of interpreting
    metalanguage formulas. Implemented using an underlying `Assignment` object
    (which in turn outsources work to `collections.ChainMap`)."""
    def __init__(self, assignment, domain=None, setfun=True, strict_charfuns=True):
        """
        Parameters
        ----------
        assignment: collections.abc.Mapping
            a mapping to initialize the model with. Values must be type domain
            elements or `meta.meta.MetaTerm` objects that wrap them.
        domain: set or dict
            Zero or more domain restrictions for type domains. If a set is
            provided, the type domain is inferred from set elements. If a
            mapping is provided, it should be a mapping from types in the
            current type system to sets of domain elements.
        setfun: bool, default: True
            If `True`, sets in `assignment` are treated as characterizing sets
            for functions with return type `t`. If `False`, sets are treated
            as the appropriate set type. (Note that sets can always be
            instantiated here by explicitly wrapping them in a `MetaTerm` with
            the type provided.)
        strict_charfuns: bool, default: True
            Determines the evaluation behavior for partial mapping-based
            functional domain elements. If `True`, such functions will raise
            a `meta.meta.DomainError` if they are called with a value not in
            their domain. If `False`, any characteristic functions will instead
            return false in this case. (Non-characteristic functions will
            always raise.)
        """
        self.domains = {}
        if domain:
            if isinstance(domain, collections.abc.Mapping):
                for typ in domain:
                    self.set_domain(typ, domain[typ])
            else:
                # if domain is just a set, infer its type
                self.set_domain(None, domain)
        self.assignment = Assignment()
        # don't use a dict comprehension -- incremental update allows constants
        # to be used in later definitions
        for k in assignment:
            self.assignment[k] = self._valuation(assignment[k], setfun=setfun)

        self.setfun = setfun
        self.strict_charfuns = strict_charfuns

    def __repr__(self):
        return f"Model(assignment={repr(dict(self.assignment))}, domain={repr(self.domains)}, strict_charfuns={repr(self.strict_charfuns)})"

    def _repr_pretty_(self, p, cycle):
        # XX the output here is neither python nor metalanguage code, but a
        # mix; it's very readable but looks misleadingly like something might
        # parse it
        if cycle:
            p.text("Model(...)")
        else:
            ctor = pretty.CallExpression.factory(self.__class__.__name__)
            p._define_context = True
            p.pretty(ctor(assignment=dict(self.assignment), domain=self.domains, strict_charfuns=self.strict_charfuns))

    def _domain_latex(self):
        r = ""
        for k in self.domains:
            r += ensuremath(f"D_{{{utils.latex_repr(k)}}} = {utils.set_latex_repr(self.domains[k], use_renames=False)}") + "<br />"
        if r:
            prefix = "**Domain**: "
            if len(self.domains) > 1:
                prefix += "<br />"
            r = prefix + r
        return r

    def _repr_markdown_(self):
        r = self._domain_latex()
        if self.assignment:
            with self.under_assignments():
                r += f"**Valuations**:<br />{self.assignment.latex_str(use_renames=False)}"

        if not r:
            return "**Empty model**"
        else:
            return r

    def _valuation(self, m, setfun=True):
        def valuation_normalize(e):
            if isinstance(e, collections.abc.Hashable) and e in self:
                # shortcut -- allow using our own values in subsequent
                # definitions. This does *not* involve evaluating anything.
                return self[e]
            elif isinstance(e, collections.abc.Set):
                return {valuation_normalize(x) for x in e}
            elif isinstance(e, collections.abc.Mapping):
                return {valuation_normalize(x): valuation_normalize(e[x]) for x in e}
            elif isinstance(e, tuple) or isinstance(e, list):
                return tuple(valuation_normalize(x) for x in e)
            else:
                return e

        return MetaTerm(valuation_normalize(m), setfun=setfun)

    def copy(self):
        return Model(self.assignment.copy(), self.domains.copy(),
                    setfun=self.setfun, strict_charfuns=self.strict_charfuns)

    def __getitem__(self, k):
        return self.assignment[k]

    def __setitem__(self, k, v):
        """Set a key according to a value `v`. Values must be either domain
        elements, or `meta.meta.MetaTerm` objects that wrap them, as in the
        constructor.

        In some cases, it is useful to relax this value constraint. A
        straightforward recipe for this given a model `m` is
        ``collections.ChainMap({}, m)``.

        See also
        --------
        `meta.core.subassignment`
        """
        self.assignment[k] = self._valuation(v, setfun=self.setfun)

    def __len__(self):
        return len(self.assignment)

    def __delitem__(self, k):
        """Delete the value for a key. This has similar behavior to deletion
        in a regular `collections.ChainMap` -- so it may reveal another value
        for the key that was shadowed, rather than resulting in no value for
        that key."""
        del self.assignment[k]

    def __iter__(self):
        return iter(self.assignment)

    def set_domain(self, typ, domain):
        """Set a domain at some type.

        Parameters
        ----------
        typ: types.TypeConstructor or None
            If `typ` is `None`, attempt to infer the type from `domain`,
            otherwise, use the indicated type.
        domain: set or None
            A set of domain elements or `MetaTerm` objects wrapping domain
            elements at the appropriate type. If `None`, the domain mapping
            for `typ` will be removed. At least one of `typ` and `domain`
            must be non-`None`.
        """
        if domain is None:
            if typ is None and len(self.domains) > 1:
                raise ValueError("Ambiguous `set_domain` call, no type provided")
            if typ in self.domains:
                del self.domains[typ]
            return
        # use the MetaTerm constructor to ensure a coherent set. This allows
        # typ=None.
        mset = MetaTerm(domain, typ=typ)
        if not isinstance(mset.type.content_type, BasicType):
            raise ValueError(f"Model domains can only be set for atomic types (got `{repr(mset.type)}`).")
        self.domains[mset.type.content_type] = {MetaTerm(e) for e in mset.op}

    def get_domain(self, typ):
        """Return the domain for `typ`, or `None` if there is no domain
        restriction at that type."""
        if not typ in self.domains:
            return None
        else:
            return self.domains[typ]

    @contextlib.contextmanager
    def under_assignments(self):
        """Temporarily apply all assignment values encoded in this model to
        the global namespace. This is a wrapper for `Assignment.under`.

        Yields
        ------
        AttrWrapper
            A wrapped version of `self`.
        """

        with self.assignment.under():
            yield utils.AttrWrapper(self)

    @contextlib.contextmanager
    def under_domains(self):
        """Temporarily apply all domain restrictions encoded in this model to
        the relevant type domains."""
        with contextlib.ExitStack() as stack:
            for typ in self.domains:
                stack.enter_context(typ.restrict_domain(self.domains[typ]))
            yield

    @contextlib.contextmanager
    def under(self):
        """Temporarily apply all assumptions encoded in this model to
        both the relevant type domains and to the global namespace.

        Yields
        ------
        AttrWrapper
            A wrapped version of `self`.

        See also
        --------
        `Namespace.under`, `Assignment.under`
        `CompositionSystem.under_model`: a wrapper on this function
        `CompositionSystem.assume_model`: for long-running model-based assumptions
        """
        with self.under_domains():
            with self.under_assignments():
                yield utils.AttrWrapper(self)

    def apply(self):
        """Apply both domain restrictions and assignment values encoded in this
        model to current global state."""
        # exceptions in the middle of these may leave things in a fairly
        # undefined state, with changes partially applied...
        get_type_system().modify_domains(self)
        global_namespace().modify(self)

    def __call__(self, e, **kwargs):
        """Evaluate `e` (wrapped for `evaluate`)"""
        return self.evaluate(e, **kwargs)

    def evaluate(self, e, simplify=True):
        """Evaluate `e` in the context of this model. This applies the
        assignment values to `e`, optionally simplifying (using any domain
        restrictions), and returns the result.

        Parameters
        ----------
        e : meta.core.TypedExpr or Assignment
            An expression or assignment to evaluate. If an `Assignment` is
            provided, this recurses and evaluates every value in the assignment.
        simplify : bool, default: True
            Whether to attempt to simplify. This does two simplification
            passes; it first reduces, then does the assignment substitution,
            then does a regular simplify pass. Note that any domain restrictions
            will likely have no impact if this is set to `False`.

        Returns
        -------
        An evaluated expression or assignment. Assignments are updated via
        `new_child`, so history is preserved.
        """
        if isinstance(e, Assignment):
            m = e.new_child()
            for k in e:
                if e[k].meta():
                    continue
                m[k] = self.evaluate(e[k], simplify=simplify)
            return m
        # otherwise, should be a TypedExpr...
        with self.under():
            # pre-simplification pass
            if simplify:
                e = e.simplify_all(reduce=True, strict_charfuns=self.strict_charfuns)
            e = e.under_assignment(self)
            if simplify:
                e = e.simplify_all(
                            evaluate=True,
                            assignment=self,
                            strict_charfuns=self.strict_charfuns)
            return e

