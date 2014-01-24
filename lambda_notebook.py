#!/usr/bin/env python3
import sys, os, signal

# see branded notebook recipe here: https://gist.github.com/timo/1497850

try:
	import IPython
	from IPython.html import notebookapp
except ImportError:
	print("You don't seem to have IPython installed, or the dependencies of ")
	print("ipython notebook are not met.")
	raise

def launch_lambda_notebook(args):
	base_path = os.path.abspath(os.path.dirname(__file__))
	sys.path.append(base_path) # perhaps not needed here
	setupscript = os.path.join(base_path, "lamb_setup.py")

	app = notebookapp.NotebookApp()


	nb_path_opt = '--NotebookManager.notebook_dir="%s"' % (os.path.join(base_path, "notebooks"))
	# this option calls a setup script that injects some environment variables
	# exec_lines needs to be passed as a command line option so that it gets correctly passed on to the kernel.
	# This should be simpler to do with exec_files, but I just could not make it work (not sure why)
	# TODO: this may cause some user specific configuration to get ignored? test
	injection_path_opt = '--IPKernelApp.exec_lines=["import sys; sys.path.append(\\"%s\\"); import lamb_setup"]' % base_path

	app.initialize([nb_path_opt, injection_path_opt] + args[1:])

	# this was in the recipe, but seems to be obsolete
	#signal.signal(signal.SIGINT, signal.default_int_handler)
	 
	try:
		app.start()
	except KeyboardInterrupt:
		pass
	finally:
		pass

if __name__ == "__main__":
	launch_lambda_notebook(sys.argv)