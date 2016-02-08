#!/usr/bin/env python3
import sys, os, signal

# see branded notebook recipe here: https://gist.github.com/timo/1497850
# refactored into lamb.setup

try:
	import IPython
	from notebook import notebookapp
	import lamb
except ImportError:
	print("You don't seem to have IPython installed, or the dependencies of ")
	print("ipython notebook are not met, or the lambda notebook library can't be found.")
	raise

def launch_lambda_notebook(args):
	# assume we are running in the repository filesystem: this script will have an adjacent directory called "notebooks".
	# can modify this for custom installations.
	import lamb.lnsetup
	base_path = os.path.abspath(os.path.dirname(__file__))
	#sys.path.append(base_path)
	#os.chdir(base_path)
	lamb.lnsetup.launch_lambda_notebook(args, nb_path=os.path.join(base_path, "notebooks"), lib_dir=base_path)
	#lamb.lnsetup.launch_lambda_notebook(args, nb_path=None, package_nb_path=os.path.join(base_path, "notebooks"))
	#lamb.lnsetup.launch_lambda_notebook(args)

if __name__ == "__main__":
	launch_lambda_notebook(sys.argv)