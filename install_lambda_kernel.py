#!/usr/bin/env python3
import sys, os, signal, argparse

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
	parser = argparse.ArgumentParser(description=
		"Install lambda notebook kernels. Use this script to install a kernel "
		"when working with the lambda notebook version in repository, or to "
		"test installations. Use `jupyter kernelspec list` to check what is "
		"installed and where.")
	parser.add_argument('--no-force-path', action='store_true',
		help='Install a kernel that uses a system-installed `lamb` module. If not set (the default), the kernel forces use of the `lamb` module in the current directory.')
	parser.add_argument('--dev', action='store_true',
		help='Install a kernel named with `-dev`. Use this to have a kernel that co-exists with an system-installed one.')
	parser.add_argument('--system', action='store_true',
		help='Install the kernel in the system prefix directory, respecting environments; if not set (the default), use the per-user. If a user and system kernel with the same name are installed, the per-user version will take priority.\nThe current system prefix is: `%s`' % sys.prefix)
	args = parser.parse_args()

	if args.dev:
		suffix = "-dev"
	else:
		suffix = ""

	if args.no_force_path:
		lib_dir = None
	else:
		# TODO: derive the path from where the `lamb` module is instead?
		lib_dir = os.path.abspath(os.path.dirname(__file__))

	r = lamb.lnsetup.install_kernelspec(lib_dir=lib_dir, user=not args.system, suffix=suffix)
	result_msg = "Lambda notebook%s kernel installed in '%s'" % (suffix, r)
	if lib_dir:
		result_msg += ", using lamb module location '%s'" % lib_dir
	print(result_msg)
	if args.system and not r.startswith(sys.prefix):
		print("Warning: system install of kernel is shadowed by a per-user lambda notebook kernel; use `jupyter kernelspec` to remove.")
