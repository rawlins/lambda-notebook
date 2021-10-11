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
* current development version: download the repository and ensure you have Jupyter installed (probably via anaconda). Run `./install_lambda_kernel.py`.

## Getting started

To run the notebook relative to the repository file structure:
  * On a mac, double click `lambda_notebook.command`.
  * Or, from a shell, run `lambda_notebook.py`.  On windows you may need to explicitly call something like `python3 lambda_notebook.py`.
  * To user a notebook directory other than the default `notebooks`, you can call something like `./lambda_notebook.py --notebook-dir=~/Documents/notebooks/`. I recommend not keeping your working notebooks in the repository copy.
  * Once the lambda-notebook kernel is installed, you can open lambda notebook files from any instance of Jupyter Notebook.

This will start a server in the terminal and open your web browser to the notebook directory.  Then, look through the various notebooks to see examples of what can be done.  I recommend starting (for now) with:
  * Lambda Notebook Intro (start here).ipynb
  * Lambda Notebook Demo.ipynb
  * look through the various fragments and tutorials

To stop the server from a terminal, hit Ctrl-C twice in the terminal window.  (To stop it from the 0.5 app, hit "Cancel".)

### Upgrading

In most instances, you can upgrade by simply downloading a new repository version and running the lambda notebook from within there (or, minimally, running `install_lambda_kernel.py` from the new repository). Your old notebooks will typically work -- the notebook format is forward compatible, and I try to avoid metalanguage regressions, but because of the alpha state, the API may change. (There may be metalanguage changes before beta, though.)

### A note on the lambda notebook UI

  * Lambda notebook is running within the Jupyter notebook framework, and inherits much of the AI. It works in either classic notebook mode or in jupyter lab.
  * Jupyter UI is modal; this can take some getting used to if you aren't familiar with modal editors such as `vi`.  Basically, you are either in edit mode (for editing cells) or command mode (for running cells).  Use Enter/esc (or mouse click inside/outside of an edit area) to switch between those.  There will be a little pen marker in the upper right corner if you are in edit mode, and the selected cell border will be green.  If something isn't doing what you expect, check if you are in the correct mode.
  * Try running through the UI tour (from the help menu of any notebook) to get a sense of the Jupyter UI.

## Code overview

There are three main parts to the code, structured into `meta.py` ("meta" for metalanguage), `types.py`, and `lang.py`.
  * `meta.py` and `types.py` together provide a typed logical metalanguage somewhat comparable to `nltk.sem`.  
  * `lang.py` provides machinery for doing composition on an object language.

Two additional files, magics.py and parsing.py provide support for using cell magics in the notebook to directly type expressions in the metalanguage.  See the notebooks for demos of what this looks like; better documentation coming soon!  


## NLTK

The file tree_mini.py provides nltk.tree, modified to work with the lambda notebook.  The long-term plan is to depend directly on nltk, but this isn't there yet.

See [here](https://github.com/nltk/nltk/blob/develop/LICENSE.txt) for NLTK license information (Apache license).
