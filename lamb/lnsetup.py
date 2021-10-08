import os, os.path, shutil, json, sys

try:
    import IPython
    from notebook import notebookapp
    from IPython.terminal.ipapp import TerminalIPythonApp
    from IPython.utils.tempdir import TemporaryDirectory
    from jupyter_client import kernelspec
    from traitlets.config import Config

except:
    print("Warning: Failed to load IPython/Jupyter.  Some features disabled.")

import lamb
# note: can't import this from any other module.
from lamb import utils, types, meta, lang, tree_mini, parsing, magics
from lamb import combinators

KERNEL_NAME = "lambda-notebook"

def inject_into_ipython():
    try:
        ip = get_ipython()
        # inject the module names
        ip.user_ns["lamb"] = lamb
        ip.user_ns["utils"] = lamb.utils
        ip.user_ns["types"] = lamb.types
        ip.user_ns["meta"] = lamb.meta
        ip.user_ns["lang"] = lamb.lang
        ip.user_ns["combinators"] = lamb.combinators

        # inject some convenience functions
        ip.user_ns["reload_lamb"] = reload_lamb
        ip.user_ns["Tree"] = lamb.utils.get_tree_class()
        ip.user_ns["MiniLatex"] = lamb.utils.MiniLatex
        ip.user_ns["ltx_print"] = lamb.utils.ltx_print
        ip.user_ns["te"] = lamb.meta.te
        ip.user_ns["tp"] = lamb.meta.tp
        ip.user_ns["unify"] = lamb.meta.unify
        # the following shouldn't be necessary as long as magics was imported,
        # but in some contexts, it appears that lnsetup can get imported
        # before get_ipython() works. It should be safe to rerun.
        lamb.magics.setup_magics()
    except:
        print("Failed to inject lambda notebook variables")
        raise

def reload_lamb(use_nltk_tree=None):
    # should this reload the magics?
    import imp
    imp.reload(lamb.utils)
    if use_nltk_tree is not None:
        # inherit default from currently running version. TODO: too confusing?
        lamb.utils.use_nltk = use_nltk_tree
    lamb.magics.reset_envs()
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
        print("Path not found for notebooks to install: '%s'" % package_nb_path,
                    flush=True)
        copy_nbs = False
    if package_nb_path and (copy_nbs or force):
        errors = []
        print("Attempting to copy installation notebooks from '%s' to '%s'"
                % (package_nb_path, nb_path), flush=True)
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

def kernelspec_template(name_modifier="", full_exec_path=False):
    # TODO: I've been occasionally seeing cases where not using the full
    # path somehow ends up with a completely wrong version of python, very
    # puzzling
    executable = full_exec_path and sys.executable or "python3"
    kernelspec_json = {
        "argv": [executable, "-m", "ipykernel", "-f", "{connection_file}"],
        # put the name-modifier earlier in the display name so that it renders
        # in the jupyter lab launch (which cuts off after 2 words).
        "display_name": "Lambda Notebook" + name_modifier + " (Python 3)",
        "language": "python"
    }
    return kernelspec_json

def kernelspec_exec_lines(lib_dir):
    exec_lines = ["import lamb.lnsetup", "lamb.lnsetup.ipython_setup()"]
    if lib_dir:
        # the following line is to deal with a messy escaping situation for
        # windows paths this may fail horribly on unix paths with backslashes,
        # but I don't have a better workaround for now
        lib_dir = lib_dir.replace("\\", "\\\\\\\\")
        exec_lines = (["import sys", "sys.path.insert(1,\'%s\')" % lib_dir]
                            + exec_lines)
    return exec_lines

def install_kernelspec(lib_dir=None, user=False, suffix="", prefix=None):
    # by default: install the kernelspec into the sys.prefix-based location
    # for kernels
    exec_lines = kernelspec_exec_lines(lib_dir)
    injection_argv = ["--IPKernelApp.exec_lines=%s" % x for x in exec_lines]

    kernel_name = KERNEL_NAME + suffix

    k_json = kernelspec_template(name_modifier=suffix)
    k_json["argv"].extend(injection_argv)

    with TemporaryDirectory() as td:
        kernel_dir = os.path.join(td, kernel_name)
        os.mkdir(kernel_dir)
        with open(os.path.join(kernel_dir, 'kernel.json'), 'w') as f:
            json.dump(k_json, f, sort_keys=True, indent=4)

        if not user and not prefix:
            prefix = sys.prefix
        # if you just pass this user=True, it tries to install into a global
        # system prefix rather than the current env. So we need to explicitly
        # use the current prefix.
        kernelspec.install_kernel_spec(kernel_dir, replace=True, user=user, prefix=prefix)

    location = kernelspec.find_kernel_specs()[kernel_name]
    return location

def launch_lambda_console(args, lib_dir=None):
    install_kernelspec(lib_dir)

    c = Config()
    # sadly, this app doesn't seem to use a kernel. Perhaps some day...
    #c.TerminalIPythonApp.kernel_name=KERNEL_NAME
    c.InteractiveShellApp.exec_lines = kernelspec_exec_lines(lib_dir)

    app = TerminalIPythonApp.instance(config=c)
    app.initialize(argv=args[1:])
    app.start()

def launch_lambda_notebook(args, lab=False, nb_path=None, lib_dir=None,
                                package_nb_path=None):
    # originally based on branded notebook recipe here:
    #   https://gist.github.com/timo/1497850
    # that recipe is for a much earlier version of IPython, so the method is
    # quite a bit different now

    # ensure that the lambda-notebook kernelspec is installed
    install_kernelspec(lib_dir)

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

    app = None
    if lab:
        try:
            from jupyterlab import labapp
            app = labapp.LabApp(config = c)
        except:
            print("Failed to start jupyterlab, falling back on notebook.")
            app = None
    if app is None:
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

