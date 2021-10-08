import shutil, os, sys, glob, pathlib
from setuptools import setup

pjoin = os.path.join
here = os.path.abspath(os.path.dirname(__file__))

# everything but the kernelspec construction is in setup.cfg
setup_args = dict()

# construct a kernelspect to install and include it in data_files.
# based on how `ipykernel` does this
if any(a.startswith(('bdist', 'install')) for a in sys.argv):
    sys.path.insert(0, here)
    import lamb.lnsetup
    # from ipykernel.kernelspec import write_kernel_spec, make_ipkernel_cmd, KERNEL_NAME

    dest = os.path.join(here, 'data_kernelspec')
    if os.path.exists(dest):
        shutil.rmtree(dest)

    # TODO: I don't see how this can work on windows, dbl check
    lamb.lnsetup.install_kernelspec(prefix=dest)

    # possibly os.path.join should be used here (per setuptools docs?, but this
    # is how the models I'm working on do it.
    ks_paths = []
    # the appropriate install path is already accomplished by the install fn
    # above, because it uses kernelspec.install_kernel_spec. However, we have
    # to reconstruct the paths correctly when building the data_files list.
    # Use some handy pathlib code for this.
    for (path, directories, filenames) in os.walk('data_kernelspec'):
    	for f in filenames:
    		ks_paths.append(pathlib.Path(path, f))

    # seems to choke if the file to install is a pathlike?
    setup_args['data_files'] = [
        (p.relative_to('data_kernelspec').parent, [str(p),]) for p in ks_paths]

if __name__ == '__main__':
    setup(**setup_args)
