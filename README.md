# Lambda Notebook: Formal Semantics with Jupyter and Python

This project is a framework for linguists and especially semanticists developing analyses in compositional semantics.  It aims to provide a means of developing 'digital fragments', following from the method of fragments in Montague grammar.

The project is in an alpha state.  While code is publicly up on github, expect bugs and rapid (or occasionally, not-so-rapid) changes.  Contributions, requests, and suggestions are welcome.  To see an example, a pre-rendered demo notebook can be found at [http://nbviewer.jupyter.org/github/rawlins/lambda-notebook/blob/master/notebooks/Lambda%20Notebook%20Demo%20%28executed%29.ipynb](http://nbviewer.jupyter.org/github/rawlins/lambda-notebook/blob/master/notebooks/Lambda%20Notebook%20Demo%20%28executed%29.ipynb).

The lead developer for this project is [Kyle Rawlins](http://sites.krieger.jhu.edu/rawlins/), kgr at jhu dot edu. I'm an associate professor in the Cognitive Science Department at Johns Hopkins University, and I do both theoretical linguistic semantics and more computational semantics. My eventual goal is for any theoretical linguistics I do to come with a lambda notebook file. (I'm a long way from that dream.)

While this repository comes with many demo and documentation notebooks, they are mostly saved unexecuted. If you would like to see some samples in nbviewer without downloading anything, the [notebook-collection](https://github.com/rawlins/notebook-collection) repository mirrors the (non-documentation) notebooks, but they are all pre-executed. Here are four samples.  The SVG MathJax renderer is highly recommended for viewing any of these (to select it, right click on any formula).

* [Continuations and Quantifier scope](http://nbviewer.jupyter.org/github/rawlins/notebook-collection/blob/master/lambda-notebook/fragments/Continuations%20and%20quantifier%20scope.ipynb), implementing the 2002 proposal by Chris Barker.
* [Intensional scope](http://nbviewer.jupyter.org/github/rawlins/notebook-collection/blob/master/lambda-notebook/fragments/Intensional%20scope.ipynb): three treatments of scope with respect to intensional items, building on the von Fintel & Heim lecture notes, work by Orin Percus, and by Ezra Keshet.
* [Intro to neo-Davidsonian event semantics](http://nbviewer.jupyter.org/github/rawlins/notebook-collection/blob/master/lambda-notebook/fragments/Neo-davidsonian%20event%20semantics.ipynb).
* [Compositional DRT](http://nbviewer.jupyter.org/github/rawlins/notebook-collection/blob/master/lambda-notebook/fragments/Compositional%20DRT.ipynb) (notebook by Dee Ann Reisinger) showing how to implement the basics of compositional DRT.

## Installation

See [https://github.com/rawlins/lambda-notebook/wiki/Installation](https://github.com/rawlins/lambda-notebook/wiki/Installation)

Basically,
* current release: install from PyPI. (`pip install lambda-notebook`.)
* current development version: download the repository and ensure you have Jupyter installed (probably via anaconda). Run `./install_lambda_kernel.py` from the repository root to
install the kernel.

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

  * Lambda Notebook Intro (start here).ipynb
  * Lambda Notebook Demo.ipynb
  * look through the various fragments and tutorials

### Upgrading

If you are working from the repository, and have installed the kernel from the
repository, you have effectively an "editable install", and the kernel will
use the repository version directly.

### A note on the lambda notebook UI

  * Lambda notebook is running within the Jupyter notebook framework, and inherits much of the AI. It works in either classic notebook mode or in jupyter lab.
  * Jupyter UI is modal; this can take some getting used to if you aren't familiar with modal editors such as `vi`.  Basically, you are either in edit mode (for editing cells) or command mode (for running cells).  Use Enter/esc (or mouse click inside/outside of an edit area) to switch between those.  There will be a little pen marker in the upper right corner if you are in edit mode, and the selected cell border will be green.  If something isn't doing what you expect, check if you are in the correct mode.
  * Try running through the UI tour (from the help menu of any notebook) to get a sense of the Jupyter UI.

## Code overview

There are three main parts to the code, structured into `meta` and submodules ("meta" for metalanguage),
`types.py`, and `lang.py`.
  * `meta` and `types.py` together provide a typed logical metalanguage somewhat comparable to `nltk.sem`.  
  * `lang.py` provides machinery for doing composition on an object language.

Two additional files, `magics.py` and `parsing.py` provide support for using
cell magics in the notebook to directly type expressions in the metalanguage.
See the notebooks for demos and documentation.

## NLTK

The file tree_mini.py provides nltk.tree, modified to work with the lambda notebook.

See [here](https://github.com/nltk/nltk/blob/develop/LICENSE.txt) for NLTK license information (Apache license).
