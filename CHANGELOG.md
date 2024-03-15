# Changelog for `lambda-notebook`

## Unreleased

The next release will be 0.8.0, and involves a major metalanguage/type system
update, centered around a new approach to metasemantics.

New features:

- Meta-meta-language (new module, `lamb.meta.meta`):
    - `MetaTerm`: this is a major change/improvement to how constant values
      (e.g. `True`) work. A `MetaTerm` is a direct, immutable reference to
      a backing python object that provides a metasemantics for the term. This
      change goes together with an explicit implementation of domain sets of
      python objects, providing backing domains for all simple types (e.g.
      type e is backed by strings of a certain kind, `SetType` is backed by
      python sets, functions are backed by mappings/callables, etc).
    - Simplification guarantees complete simplification when dealing with
      `MetaTerm`s. This change also allows simplification for quantified
      expressions with finite domains (by iterating over the type domain).
    - `Evaluations`: much richer support for truth-table-like batch evaluations
      of boolean expressions. `truthtable` is a handy wrapper function on this.
    - `extract_boolean`: given an arbitrary metalanguage expression, produce
      a purely boolean expression together with an assignment filling in the
      non-boolean parts.
- Metalanguage set operations and relations
    - core operations: intersection, union, difference. Core relations:
      equivalence, the various sub/superset relations.
    - corresponding simplification heuristics.
- Type system features:
    - As noted above, the ontology for simple types is new essentially complete,
      at least for the finite case, by implementing domain sets.
    - Type domains allow domain restriction in order to work with finite
      examples. The easiest api for this is the context manager function
      `restrict_domain` on atomic types.
    - A new type constructor (∀) that unselectively binds type variables in its
      scope. This is only semi-intended to be user facing, as it isn't easy
      to understand. However, this directly supports the next feature:
    - Support for full let-polymorphism via assignments. That is, polymorphic
      functions in assignments can now have distinct specializations in the
      same expression (previously they would have to unify to a coherent type;
      let-polymorphism could only be achieved anonymously via reduction).
- Metalanguage "compilation": expressions with no free variables can now be
  converted to python code that runs roughly within an order of magnitude of
  similar code implemented directly in python. In many cases, this is *much*
  faster than simplification, and sometimes in a way that matters (especially
  with quantification in play). There are certain other caveats: finite sets
  only, equivalence of functions can't be dynamically determined.
- Simplification and expression manipulation features:
    - new module, `lamb.meta.ply`, hosts various code (new and old) for generic
      manipulation and introspection on `TypedExpr` objects.
    - term order normalization for n-ary operations where this is appropriate
      (e.g. &, |). This normalizes order and structure (to left commutivity).
      This approach allows keeping strict binary operators, but when
      appropriate, manipulating them as n-ary sequences.
    - more configurable simplification, with a number of options that may not
      be used by default. (Roughly building on SymPy's approach.) For example,
      the `eliminate_sets` option will convert set operations/relations to
      booleans where possible, though this may make formulas more complicated.
- Error / exception handling and display, especially in magic contexts, is
  rewritten. New context manager `lamb.errors()` allows clean handling of
  lambda notebook-specific errors.
- Composition:
    - compose order is now preserved and used in rendering for bottom-up
      composition.
    - composition objects now support a function `source_tree()`, which extracts
      an underlying nltk-style `Tree` for display.

Documentation and sample notebooks:

- New documentation for sets, meta-meta-language expressions
- Rewritten: Hamblin semantics fragment

Fixes, improvements, changes:

- types and related issues:
    - many internal improvements/changes to type inference. One thing to note is
      that internal type variables will now appear as `?` followed by a number,
      rather than as `I` variables.
    - improvements to anonymous let-polymorphism, which was previously very
      non-general
    - Many bug fixes to do with polymorphism
- improvements to simplification with recursive `Tuple` expressions
- improvements to inference for `Partial` expressions.
- improvements to `derivation`s. The most public-facing change is that
  derivation reasons are now visually aligned with the origin step, not the
  result step. These objects now better support introspection, as well.
- many improvements to metalanguage simplification and reduction heuristics.
- improvements to latex rendering compatibility, including colab (katex) and
  mathjax 3.
- Older support code has been removed

## [0.7.0] - Rendering and metalanguage updates - 2023-09-27

New features:
 - support rendering in colab
 - quicker loading without the kernel (`import lamb.auto`)
 - refactor metalanguage code: better support for new operators

 Fixes:
 - fix several polymorphic type inference issues
 - improved ipython/jupyter rendering

## [0.6.9] - Compatibility fix - 2022-06-18

Fix a python 3.10 compatibility bug

## [0.6.8] - Vacuity improvements - 2021-10-18

Fixes, improvements, changes (highlights):
 - correctly pin the right traitlets version

## [0.6.7] - Vacuity improvements - 2021-10-18

New features:
 - composition rule for index percolation in tree composition
 - composition rule for vacuous nodes (with content=None)

Fixes, improvements, changes (highlights):
 - improve and generalize lang.Binder behavior
 - enable svgling for internal tree drawing
 - improvements to the relative clause notebook

## [0.6.6] - Bugfix release - 2021-10-11

New features:
 - added an explicit changelog
 - experimental support for derivations shown using `svgling` trees
 - full support for installation in `site-packages`, better kernel installation

Fixes, improvements, changes (highlights):
 - improve derivation rendering
 - improve cross-browser compatibility
 - improve error messaging and handling of composition failures
