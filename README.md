# Lambda Notebook: Formal Semantics with Jupyter and Python

**Author**: Kyle Rawlins, [kgr@jhu.edu](mailto:kgr@jhu.edu)

**Website**: https://rawlins.github.io/lambda-notebook/

**Repository**: https://github.com/rawlins/lambda-notebook

This project is a framework for linguists and especially semanticists developing analyses in compositional semantics.  It aims to provide a means of developing 'digital fragments', following from the method of fragments in Montague grammar. Contributions, requests, and suggestions are welcome. To see some examples of the project in action, Have a look at the [demo page](https://rawlins.github.io/lambda-notebook/demo-for-linguists.html), which is pre-rendered from an interactive Jupyter document. The project itself comes with many more examples, though you will need to download and work with them interactively: https://github.com/rawlins/lambda-notebook/tree/master/notebooks

The lead developer for this project is [Kyle Rawlins](https://rawlins.io/). I'm an associate professor in the Cognitive Science Department at Johns Hopkins University, and I do both theoretical linguistic semantics and computational semantics. My eventual goal is for any theoretical linguistics I do to come with a lambda notebook file. (I'm a long way from that dream.)

## Installation

See [https://github.com/rawlins/lambda-notebook/wiki/Installation](https://github.com/rawlins/lambda-notebook/wiki/Installation)

Basically,
* Install Jupyter Lab.
* current release: install from PyPI. (`pip install lambda-notebook`.) 
* current development version: download/clone the repository and ensure you have Jupyter installed (probably via anaconda). Run `./install_lambda_kernel.py` from the repository root to
install the kernel.
* See the above link for information on using the package on colab. VSCode and other Jupyter notebook interfaces are not supported.

## Getting started

Once you have installed the package, you can then open open lambda notebook
files by using the newly installed kernel from any jupyter lab (or notebook)
instance. The kernel for regular installs is named `Lambda notebook (Python 3)`,
and it can be selected as a new kernel from the launcher, or via the
`Change Kernel...` menu item in the `Kernel` menu.

Alternatively, with the `lamb` module installed in the python path, you can
run `import lamb.auto`, which is fully equivalent to loading a notebook with
the kernel.

I recommend starting with some of the notebook files in this repository.

  * `notebooks/Lambda Notebook Intro (start here).ipynb`
  * `docs/demo-for-linguists.ipynb`
  * look through the various [fragments](https://github.com/rawlins/lambda-notebook/tree/master/notebooks/fragments) and [documentation notebooks](https://github.com/rawlins/lambda-notebook/tree/master/notebooks/documentation)

## Code overview

There are three main parts to the code, structured into `lamb.meta` and submodules ("meta" for metalanguage),
`lamb.types`, and `lamb.lang`.
  * `meta` and `types` together provide a typed logical metalanguage. Some of `meta`'s key submodules:
    - `lamb.meta.core`: core machinery for typed expressions and functions
    - `lamb.meta.boolean`: boolean expressions
    - `lamb.meta.quantifiers`: quantified expressions
    - `lamb.meta.sets`: set theoretic expressions
    - `lamb.meta.meta`: meta-meta-language expressions
    - `lamb.meta.ply`: tools for manipulating metalanguage expressions
  * `lamb.types` provides implementations of type systems for a simply typed lambda calculus, a polymorphic lambda calculus using the "Damas-Hindley-Milner" type system, and various accessories.
  * `lamb.lang` provides machinery for doing composition on an object language.

Two additional files, `magics.py` and `parsing.py` provide support for using
cell magics in the notebook to directly type expressions in the metalanguage.
See the notebooks for demos and documentation.

## License information

The lambda notebook is released under the [BSD 3-clause license](https://github.com/rawlins/lambda-notebook/blob/master/LICENSE).

The module `lamb.tree_mini` provides a modified and dependency-less version of the `nltk.tree` module from the [nltk package](https://www.nltk.org/). See [here](https://github.com/nltk/nltk/blob/develop/LICENSE.txt) for NLTK license information (Apache license).
