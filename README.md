# IPython Lambda Notebook

This project is a framework for linguists and especially semanticists developing analyses in compositional semantics.  It aims to provide a means of developing 'digital fragments', following from the method of fragments in Montague grammar.

The project is in an alpha state.  While code is publicly up on github, expect bugs and rapid changes.  Contributions, requests, and suggestions are welcome.  I hope to have a more stable beta by the end of summer 2014.

If you are interested in discussing this project, you can join the following mailing list, which currently very low traffic: [http://lists.lambdanotebook.com/listinfo.cgi/lnb-dev-lambdanotebook.com](http://lists.lambdanotebook.com/listinfo.cgi/lnb-dev-lambdanotebook.com).  You can also ask questions directly to Kyle Rawlins, [kgr@jhu.edu](mailto:kgr@jhu.edu).

## Installation

Prerequisites: python 3.3.x, and IPython 2.0+.  

The easiest way to install is probably via [macports](http://www.macports.org/).  If you are using Macports, the following installation steps should get it running from scratch: (thanks to Robert Adesam for these)

  1. sudo port install python33 py33-ipython py33-zmq py33-jinja2 py33-tornado
  2. sudo ln -s /opt/local/bin/python3.3 /opt/local/bin/python3
  3. curl -O https://codeload.github.com/rawlins/lambda-notebook/zip/master
  4. unzip master
  5. cd lambda-notebook-master
  6. ./lambda_notebook.py

Manual installation is possible if you are familiar with python package management.  Here are some notes:

  * For python 3, see [http://www.python.org/](http://www.python.org/).  We do not recommend using OS installed versions, for example, on OS X; installing an up-to-date version of python 3 is however very easy.
  * The complications lie in getting IPython to work with python 3.  _Note_: this should be drastically simplified in IPython 2.0, but this hasn't yet been tested.  (Reports welcome!)
  * For general installation instructions for IPython, see [http://ipython.org/install.html](http://ipython.org/install.html).  A slightly outdated, but more useful document, is at [http://ipython.org/ipython-doc/rel-1.1.0/install/index.html](http://ipython.org/ipython-doc/rel-1.1.0/install/index.html).  
  For IPython notebook, you will need to make sure you have installed the packages pyzmq, Jinja2, nose, Tornado, readline.  To install several of these on a mac, you will need an XCode installation first; this can be downloaded for free from the app store.  Once xcode is installed, you will need to install the xcode command line tools.  Then you should install them using easy_install (part of setup_tools) or pip.  (_These notes need to be expanded, and adapted for windows..._)
  * To run ipython with python 3, you can either install IPython by using 'python3 setup.py' or easy_install-3.3 or whatever, or run 'python3 ipython.py'.  
  * Suggestions for improving these instructions are welcome!  The long term goal is to provide the lambda notebook as a standalone app.



## Getting started

To run the notebook:
  * On a mac, double click `lambda_notebook.command`.
  * Or, from a shell, run `lambda_notebook.py`.  On windows you may need to explicitly call something like `python3 lambda_notebook.py`.  (Untested.)
  * To user a notebook directory other than the default `notebooks`, you can call something like `./lambda_notebook.py --notebook-dir=./local_notebooks/`.  Note that `local_notebooks` is untracked by git, so is a safe place to put testing notebooks etc.
  * IPython 2 includes a directory browser, and `notebooks/local_notebooks` is also untracked.

This will start a server in the terminal and open your web browser to the notebook directory.  Then, look through the various notebooks to see examples of what can be done.  I recommend starting (for now) with:
  * Lamb demo
  * LSA Poster examples
  * Relative clauses
  * Variable free binding (as an example of a reasonably worked out interactive fragment)
  * Type shifting

The following two demonstrate some ways of extending the library system:
  * definite articles tutorial
  * Composition operations

To stop the server, hit Ctrl-C twice in the terminal window.

It is also possible to load most of the facilities of the lambda notebook directly into a regularly-started notebook, or into an arbitrary (i)python 3 instance, by adding the base directory of the lambda notebook to the modules path, and then importing `lamb_setup` (or directly importing the relevant modules).

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