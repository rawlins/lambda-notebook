#!/usr/bin/env python3
import sys, os, signal

# utility for installing various versions of the lambda notebook kernel in
# various places, for development purposes. Actual installation code is in
# lamb.lnsetup.

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
	suffix = ""
	user = False
	# TODO: actual cli handling
	if len(sys.argv) > 1 and sys.argv[1] == "--force-path":
		lib_dir = os.path.abspath(os.path.dirname(__file__))
		suffix = "-dev"
		user = True
	r = lamb.lnsetup.install_kernelspec(lib_dir=lib_dir, user=user, suffix=suffix)
	result_msg = "Lambda notebook kernel installed in '%s'" % r
	if lib_dir:
		result_msg += ", using lamb module location '%s'" % lib_dir
	print(result_msg)
