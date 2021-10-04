#!/usr/bin/env python3
import sys, os, signal

# see branded notebook recipe here: https://gist.github.com/timo/1497850
# refactored into lamb.setup

try:
	import IPython
	from notebook import notebookapp
	import lamb
except ImportError:
	print("You don't seem to have IPython/Jupyter installed, or the dependencies of ")
	print("Jupyter notebook are not met, or the lambda notebook library can't be found.")
	print("Have you tried running `pip3 install jupyter` at the command line?")
	raise

if __name__ == "__main__":
	import lamb.lnsetup
	lib_dir = None
	if len(sys.argv) > 1 and sys.argv[1] == "--force-path":
		lib_dir = os.path.abspath(os.path.dirname(__file__))
	r = lamb.lnsetup.install_kernelspec(lib_dir=lib_dir)
	print("Lambda notebook kernel installed in '%s' using python executable '%s'" % (r, sys.executable))
