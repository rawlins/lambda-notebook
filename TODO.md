
## Interface / app improvements

### Standalone app

 * Lots of ways to go.
 * For mac, build off of [https://github.com/liyanage/ipython-notebook](https://github.com/liyanage/ipython-notebook), looks great.
 * PC: will take a while, I don't even have a windows installation.

### Misc ideas

 * Graph / tree drawing via javascript injection.  Use [https://github.com/cpettitt/dagre](https://github.com/cpettitt/dagre) with d3?

## Notebook content improvements

### Metalanguage

 * better parsing (in progress)
 * presuppositions
 * better handling of programmatic construction
    - e.g. properly handle types in something like `meta.LFun(lang.tp("<e,t>"), "f(x_e)", "f")`
    - automatic variable name selection in BindingOp construction


### Notebooks

 * More examples!