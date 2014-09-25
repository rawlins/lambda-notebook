#!/usr/bin/env python3
import sys, os, signal

# script for starting the notebook as part of a self-contained app

try:
	import IPython
	from IPython.html import notebookapp
	import lamb
except ImportError:
	print("You don't seem to have IPython installed, or the dependencies of ")
	print("ipython notebook are not met, or the lambda notebook library can't be found.")
	raise

def launch_lambda_notebook(args):
	# assume we are running in an app.  launch_lambda_notebook will take care of the default notebook directory (TODO: rethink?)
	# but we need to give it a place to find the initial notebooks.
	import lamb.lnsetup
	base_path = os.path.abspath(os.path.dirname(__file__))
	#sys.path.append(base_path)
	#os.chdir(base_path)
	#lamb.lnsetup.launch_lambda_notebook(args, nb_path=os.path.join(base_path, "notebooks"), lib_dir=base_path)
	lamb.lnsetup.launch_lambda_notebook(args, package_nb_path=os.path.join(base_path, "../Resources/package_notebooks"))

if __name__ == "__main__":
	launch_lambda_notebook(sys.argv)