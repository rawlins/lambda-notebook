#setup and load the lambda notebook
# this is intended to be run automatically during notebook startup.  If you want to use lambda notebook files
# without the branded version of notebook, you will need to insert some variant of these imports into the beginning 
# of your notebook.
import lamb
from lamb import *
from lamb.tree_mini import Tree
import logging

def inject():
	try:
		ip = get_ipython()
		# inject the module names
		ip.user_ns["lamb"] = lamb
		ip.user_ns["utils"] = lamb.utils
		ip.user_ns["types"] = lamb.types
		ip.user_ns["meta"] = lamb.meta
		ip.user_ns["lang"] = lamb.lang
		ip.user_ns["parsing"] = lamb.parsing

		# inject some convenience functions
		ip.user_ns["reload_lamb"] = reload_lamb
		ip.user_ns["Tree"] = lamb.tree_mini.Tree
		ip.user_ns["MiniLatex"] = lamb.utils.MiniLatex
		ip.user_ns["ltx_print"] = lamb.utils.ltx_print
		ip.user_ns["te"] = lamb.lang.te
		ip.user_ns["tp"] = lamb.lang.tp
	except:
		print("Failed to inject lambda notebook variables into the ipython kernel namespace")
		raise

def reload_lamb():
	# should this reload the magics?
	import imp
	imp.reload(lamb.utils)
	imp.reload(lamb.types)
	imp.reload(lamb.meta)
	imp.reload(lamb.lang)
	imp.reload(lamb.parsing)
	lamb.reload_all = reload_lamb
	inject()

if __name__ == "__main__":
	print("Please run 'lambda_notebook.py' to start the IPython Lambda Notebook.")
else:
	lamb.reload_all = reload_lamb
	inject()