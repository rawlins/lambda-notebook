# IPython Lambda Notebook

This project is a framework for linguists and especially semanticists developing analyses in compositional semantics.  It aims to provide a means of developing 'digital fragments', following from the method of fragments in Montague grammar.

The project is in an alpha state.  While code is publicly up on github, expect bugs and rapid changes.  Contributions, requests, and suggestions are welcome.

If you are interested in discussing this project, you can join the following mailing list, which currently very low traffic: [http://lists.lambdanotebook.com/listinfo.cgi/lnb-dev-lambdanotebook.com](http://lists.lambdanotebook.com/listinfo.cgi/lnb-dev-lambdanotebook.com).  You can also ask questions directly to Kyle Rawlins, [kgr@jhu.edu](mailto:kgr@jhu.edu).

## Installation

See [https://github.com/rawlins/lambda-notebook/wiki/Installation](https://github.com/rawlins/lambda-notebook/wiki/Installation)

## Getting started

On a mac, double click the app, and open the notebook called "Lambda Notebook Intro (start here).ipynb".

Otherwise, to run the notebook in the repository file structure:
  * On a mac, double click `lambda_notebook.command`.
  * Or, from a shell, run `lambda_notebook.py`.  On windows you may need to explicitly call something like `python3 lambda_notebook.py`.  (Untested.)
  * To user a notebook directory other than the default `notebooks`, you can call something like `./lambda_notebook.py --notebook-dir=./local_notebooks/`.  Note that `local_notebooks` is untracked by git, so is a safe place to put testing notebooks etc.
  * IPython 2 includes a directory browser, and `notebooks/local_notebooks` is also untracked.

This will start a server in the terminal and open your web browser to the notebook directory.  Then, look through the various notebooks to see examples of what can be done.  I recommend starting (for now) with:
  * Lambda Notebook Intro (start here).ipynb
  * Lambda Notebook Demo.ipynb
  * look through the various fragments and tutorials

To stop the server from a terminal, hit Ctrl-C twice in the terminal window.  To stop it from the app, hit "Cancel".

It is also possible to load most of the facilities of the lambda notebook directly into a regularly-started notebook, or into an arbitrary (i)python 3 instance, by adding the base directory of the lambda notebook to the modules path, and then importing `lamb` (or directly importing the relevant modules).

_Important note: notebooks that are part of this project assume that the lambda notebook modules (and other facilities) are part of the namespace already, and will not work without modification when loaded into a regular lambda notebook.  This typically just means importing things; see `lamb_setup.py` for an idea._


### A note on the lambda notebook UI

  * As of IPython 2.0, the UI is now modal; this can take some getting used to if you aren't familiar with modal editors such as VI.  Basically, you are either in edit mode (for editing cells) or command mode (for running cells).  Use Enter/esc (or mouse click inside/outside of an edit area) to switch between those.  There will be a little pen marker in the upper right corner if you are in edit mode, and the selected cell border will be green.  If something isn't doing what you expect, check if you are in the correct mode.
  * Try running through the UI tour (from the help menu of any notebook) to get a sense of the IPython UI.

## Code overview

There are three main parts to the code, structured into meta.py (for metalanguage), types.py, and lang.py.
  * meta.py and types.py together provide a typed logical metalanguage somewhat comparable to nltk.sem.  
  * lang.py provides machinery for doing composition on an object language.

Two additional files, magics.py and parsing.py provide support for using cell magics in the notebook to directly type expressions in the metalanguage.  See the notebooks for demos of what this looks like; better documentation coming soon!  


## NLTK

The file tree_mini.py provides nltk.tree, hacked to work in python 3.  Note that this is _not permanent_, and once nltk supports python 3 directly (in beta now) this will become part of a dependency.  I have also added IPython display routines that will in the future be installed via monkey patching.

See [here](https://github.com/nltk/nltk/blob/develop/LICENSE.txt) for NLTK license information (Apache license).