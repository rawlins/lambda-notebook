import os, os.path, shutil

try:
    import IPython
    from IPython.html import notebookapp
except:
    print("Warning: Failed to load IPython.  Some features disabled.")

import lamb
# note: can't import this from any other module.
from lamb import utils, types, meta, lang, tree_mini, parsing, magics
from lamb.tree_mini import Tree


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
    inject_into_ipython()


def ipython_setup():
    lamb.reload_all = reload_lamb
    inject_into_ipython()

def install_notebooks(nb_path, package_nb_path, force=False):
    copy_nbs = False
    if not os.path.exists(nb_path):
        os.makedirs(nb_path)
        copy_nbs = True
    if copy_nbs and not os.path.exists(package_nb_path):
        print("Path not found for notebooks to install: '%s'" % package_nb_path)
        copy_nbs = False
    if package_nb_path and (copy_nbs or force):
        errors = []
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

def launch_lambda_notebook(args, nb_path=None, lib_dir=None, package_nb_path=None):
    # see branded notebook recipe here: https://gist.github.com/timo/1497850
    #base_path = os.path.abspath(os.path.dirname(__file__))
    #sys.path.append(base_path) # perhaps not needed here
    #setupscript = os.path.join(base_path, "lamb_setup.py")

    app = notebookapp.NotebookApp()


    #nb_path_opt = '--NotebookManager.notebook_dir="%s"' % (os.path.join(base_path, "notebooks"))
    if nb_path is None:
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
    nb_path_opt = '--NotebookManager.notebook_dir="%s"' % nb_path
    # this option calls a setup script that injects some environment variables
    # exec_lines needs to be passed as a command line option so that it gets correctly passed on to the kernel.
    # This should be simpler to do with exec_files, but I just could not make it work (not sure why)
    # TODO: this may cause some user specific configuration to get ignored? test
    # note: bad things happen here if lib_dir is problematic...
    if lib_dir:
        # TODO: won't override an installed copy of lamb in site-packages (e.g. in the app), fix this
        injection_path_opt = '--IPKernelApp.exec_lines=["import sys; sys.path.append(\'%s\'); import lamb.lnsetup; lamb.lnsetup.ipython_setup()"]' % lib_dir
    else:
        injection_path_opt = '--IPKernelApp.exec_lines=["import lamb.lnsetup; lamb.lnsetup.ipython_setup()"]'


    app.initialize([nb_path_opt, injection_path_opt] + args[1:])

    # this was in the recipe, but seems to be obsolete
    #signal.signal(signal.SIGINT, signal.default_int_handler)
     
    try:
        app.start()
    except KeyboardInterrupt:
        pass
    finally:
        pass

