import os, os.path, shutil, json, sys

try:
    import IPython
    from notebook import notebookapp
    from IPython.terminal.ipapp import TerminalIPythonApp
    from jupyter_client import kernelspec
    from traitlets.config import Config

except:
    print("Warning: Failed to load IPython/Jupyter.  Some features disabled.")

import lamb
# note: can't import this from any other module.
from lamb import utils, types, meta, lang, tree_mini, parsing, magics, combinators

def inject_into_ipython():
    try:
        ip = get_ipython()
        # inject the module names
        ip.user_ns["lamb"] = lamb
        ip.user_ns["utils"] = lamb.utils
        ip.user_ns["types"] = lamb.types
        ip.user_ns["meta"] = lamb.meta
        ip.user_ns["lang"] = lamb.lang
        ip.user_ns["parsing"] = lamb.parsing
        ip.user_ns["display"] = lamb.display
        ip.user_ns["combinators"] = lamb.combinators

        # inject some convenience functions
        ip.user_ns["reload_lamb"] = reload_lamb
        ip.user_ns["Tree"] = lamb.utils.get_tree_class()
        ip.user_ns["MiniLatex"] = lamb.utils.MiniLatex
        ip.user_ns["ltx_print"] = lamb.utils.ltx_print
        ip.user_ns["te"] = lamb.meta.te
        ip.user_ns["tp"] = lamb.meta.tp
    except:
        print("Failed to inject lambda notebook variables into the ipython kernel namespace")
        raise

def reload_lamb(use_nltk_tree=None):
    # should this reload the magics?
    import imp
    imp.reload(lamb.utils)
    if use_nltk_tree is not None:
        lamb.utils.use_nltk = use_nltk_tree # inherit default from currently running version. TODO: too confusing?
    imp.reload(lamb.types)
    imp.reload(lamb.meta)
    imp.reload(lamb.lang)
    imp.reload(lamb.parsing)
    imp.reload(lamb.display)
    imp.reload(lamb.combinators)
    lamb.reload_all = reload_lamb
    inject_into_ipython()


def ipython_setup():
    lamb.reload_all = reload_lamb
    inject_into_ipython()

def install_notebooks(nb_path, package_nb_path, force=False):
    copy_nbs = False
    #TODO: this is kind of hacky
    if nb_path[0] == "~":
        nb_path = os.path.expanduser(nb_path)
    if not os.path.exists(nb_path):
        os.makedirs(nb_path)
        copy_nbs = True
    if copy_nbs and not os.path.exists(package_nb_path):
        print("Path not found for notebooks to install: '%s'" % package_nb_path, flush=True)
        copy_nbs = False
    if package_nb_path and (copy_nbs or force):
        errors = []
        print("Attempting to copy installation notebooks from '%s' to '%s'" % (package_nb_path, nb_path), flush=True)
        names = os.listdir(package_nb_path)
        for name in names:
            srcname = os.path.join(package_nb_path, name)
            destname = os.path.join(nb_path, name)
            if os.path.exists(destname):
                pass # never overwrite anything
            try:
                if os.path.islink(srcname):
                    pass # ignore symlinks
                elif os.path.isdir(srcname):
                    shutil.copytree(srcname, destname)
                else:
                    shutil.copy2(srcname, destname)
            except OSError as why:
                errors.append((srcname, destname, str(why)))
            # catch the Error from the recursive copytree so that we can
            # continue with other files
            except shutil.Error as err:
                errors.extend(err.args[0])
        if errors:
            raise shutil.Error(errors)

kernelspec_str = """{
 "argv": ["python3", "-m", "ipykernel",
          "-f", "{connection_file}", "%s"],
 "display_name": "Lambda Notebook (Python 3)",
 "language": "python"
}"""

def build_json():
    if sys.version_info[0] != 3:
        raise Exception("Could not install lambda notebook kernel from non-python 3, please run with python 3.")
    executable = sys.executable
    kernelspec_json = {
        "argv": [sys.executable, "-m", "ipykernel", "-f", "{connection_file}"],
        "display_name": "Lambda Notebook (Python 3)",
        "language": "python"
    }
    return kernelspec_json

def install_kernelspec(lib_dir, kernel_dir=None, user=True):
    if kernel_dir is None:
        kernel_dir = os.path.join(lib_dir, "kernel", "lambda-notebook")

    if lib_dir:
        # TODO: won't override an installed copy of lamb in site-packages (e.g. in the app), fix this
        # the following line is to deal with a messy escaping situation for windows paths
        # this may fail horribly on unix paths with backslashes, but I don't have a better workaround for now
        lib_dir = lib_dir.replace("\\", "\\\\\\\\")
        injection_path_opt = "--IPKernelApp.exec_lines=[\"import sys\",\"sys.path.append(\\\"%s\\\")\", \"import lamb.lnsetup\", \"lamb.lnsetup.ipython_setup()\"]" % lib_dir
    else:
        injection_path_opt = "--IPKernelApp.exec_lines=[\"import lamb.lnsetup\", \"lamb.lnsetup.ipython_setup()\"]"

    k_json = build_json()
    k_json["argv"].append(injection_path_opt)
    k_json_filename = os.path.join(kernel_dir, "kernel.json")
    #print(k_json)
    with open(k_json_filename, 'w') as k_json_file:
        json.dump(k_json, k_json_file, sort_keys=True, indent=4)

    kernelspec.install_kernel_spec(kernel_dir, user=user, replace=True)
    location = kernelspec.find_kernel_specs()['lambda-notebook']
    return location

def launch_lambda_console(args, lib_dir=None, kernel_dir=None):
    install_kernelspec(lib_dir, kernel_dir)

    c = Config()
    # no idea why this doesn't work, but it doesn't...
    #c.IPythonConsoleApp.kernel_name="lambda-notebook"
    c.InteractiveShellApp.exec_lines=["import sys; sys.path.append(r\"%s\"); import lamb.lnsetup; lamb.lnsetup.ipython_setup()" % lib_dir]

    app = TerminalIPythonApp.instance(config=c)
    app.initialize(argv=args[1:])
    app.start()


def launch_lambda_notebook(args, nb_path=None, lib_dir=None, package_nb_path=None, kernel_dir=None):
    # originally based on branded notebook recipe here: https://gist.github.com/timo/1497850
    # that recipe is for a much earlier version of IPython, so the method is quite a bit different now

    
    # ensure that the lambda-notebook kernelspec is installed
    install_kernelspec(lib_dir, kernel_dir)

    c = Config()

    if nb_path is None:
        # TODO this needs to be fixed for windows...
        nb_path = os.path.expanduser("~/Documents/lambda_notebook/")
        if nb_path[0] == "~":
            raise Error("Unable to locate home directory")
        #TODO: need something more general here
    if not os.path.exists(nb_path):
        try:
            install_notebooks(nb_path, package_nb_path, force=False)
        except shutil.Error as err:
            print(err)
        #os.makedirs(nb_path)

    c.NotebookApp.notebook_dir = nb_path

    app = notebookapp.NotebookApp(config=c)

    app.initialize(args[1:])
     
    try:
        app.start()
    except KeyboardInterrupt:
        pass
    finally:
        pass

def version_str():
    s = "Lambda notebook version " + lamb.__version__
    if not lamb.__release__:
        s += " (development version)"
    return s

