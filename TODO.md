
## Interface / app improvements

### Standalone app

 * Lots of ways to go.
 * For mac, build off of [https://github.com/liyanage/ipython-notebook](https://github.com/liyanage/ipython-notebook), looks great.
 * PC: will take a while.

### Interface ideas

 * Graph / tree drawing via javascript injection.  Use [https://github.com/cpettitt/dagre](https://github.com/cpettitt/dagre) with d3?
 * Interactive outputs via javascript.  (Lots of possibilities)
   - cycle through derivations, rather than render them all at once
   - click to (un/)expand derivation trees
   - click to expand meta-language derivations
 * Streamline rendering code.  (Generalize object for rendering recursive tree-like structures?)
 * continue searching for better/faster way of rendering double brackets.

## Notebook content improvements

 * interface with some sort of parser (cf. Boxer web demo)

### Metalanguage

 * better parsing, better type inference algorithms, etc.  (Permanent TODO)
 * presuppositions / projective meaning tools
 * DRS-like support; some sort of integration with boxer?
 * better handling of programmatic construction
    - e.g. properly handle types in something like `meta.LFun(lang.tp("<e,t>"), "f(x_e)", "f")`
    - automatic variable name selection in BindingOp construction

### Composition systems

 * Lexical ambiguities (need to think about what's the right way to do this).
 * More general notion of lexicon.
 * LF manipulations.  (QR etc.)
 * Free indexing or similar mechanism.
 * Extract type-shifting into a library, document it.

### Notebooks

 * More examples!
   - continuations
   - continue vF&H notebook
   - continue Hamblin semantics notebook
   - more CG/CCG-type examples
   - concealed questions (Romero & Han)
   - degree semantics
   - spatial language / vectors (Zwarts)
   - compositional DRT (Muskens, Bittner maybe?)
   - etc.
