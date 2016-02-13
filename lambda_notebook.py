#!/usr/bin/env python3
import sys, os, signal, argparse

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

def setup_argparser():
	parser = argparse.ArgumentParser(description='Start the lambda notebook')
	parser.add_argument('--version', action='store_true', default=False)
	parser.add_argument('--install-kernel', action='store_true', default=False)
	parser.add_argument('--notebook-dir', type=str, default='')
	return parser

def launch_lambda_notebook(parsed_args, args):
	# assume we are running in the repository filesystem: this script will have an adjacent directory called "notebooks".
	# can modify this for custom installations.
	import lamb.lnsetup
	base_path = os.path.abspath(os.path.dirname(__file__))
	#sys.path.append(base_path)
	#os.chdir(base_path)
	print(lamb.lnsetup.version_str())
	print("Starting Jupyter notebook...")
	if len(parsed_args.notebook_dir) > 0:
		nb_path = parsed_args.notebook_dir
	else:
		nb_path = os.path.join(base_path, "notebooks")
	lamb.lnsetup.launch_lambda_notebook(args, nb_path=nb_path, lib_dir=base_path)
	#lamb.lnsetup.launch_lambda_notebook(args, nb_path=None, package_nb_path=os.path.join(base_path, "notebooks"))
	#lamb.lnsetup.launch_lambda_notebook(args)

def install_kernel(parsed_args):
	import lamb.lnsetup
	base_path = os.path.abspath(os.path.dirname(__file__))
	print("Installing lambda-notebook kernel for " + lamb.lnsetup.version_str())
	lamb.lnsetup.install_kernelspec(base_path)

if __name__ == "__main__":
	import lamb.lnsetup
	parser = setup_argparser()
	(args, remainder) = parser.parse_known_args()
	if args.version:
		print(lamb.lnsetup.version_str())
	elif args.install_kernel:
		install_kernel(args)
	else:
		launch_lambda_notebook(args, remainder)


