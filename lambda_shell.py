#!/usr/bin/env python3
import sys, os, signal

# see branded notebook recipe here: https://gist.github.com/timo/1497850
# refactored into lamb.setup

try:
    import IPython
    from IPython.terminal.ipapp import TerminalIPythonApp
    from jupyter_client import kernelspec
except ImportError:
	print("You don't seem to have Jupyter installed, or the dependencies of ")
	print("Jupyter notebook are not met.")
	raise
try:
	import lamb
except ImportError:
	print("The lambda notebook library can't be found; can't start a shell.")
	raise


def launch_lambda_shell(args):
	# assume we are running in the repository filesystem: this script will have an adjacent directory called "notebooks".
	# can modify this for custom installations.
	import lamb.lnsetup
	base_path = os.path.abspath(os.path.dirname(__file__))
	#sys.path.append(base_path)
	#os.chdir(base_path)
	lamb.lnsetup.launch_lambda_console(args, lib_dir=base_path)
	#lamb.lnsetup.launch_lambda_notebook(args, nb_path=None, package_nb_path=os.path.join(base_path, "notebooks"))
	#lamb.lnsetup.launch_lambda_notebook(args)

if __name__ == "__main__":
	launch_lambda_shell(sys.argv)