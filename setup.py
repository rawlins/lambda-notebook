import shutil, os, sys, glob, pathlib
from setuptools import setup

pjoin = os.path.join
here = os.path.abspath(os.path.dirname(__file__))

# everything but the package data kernelspec construction is in setup.cfg
setup_args = dict()

# Apparently we need both package_data and MANIFEST.in for both sdist and bdist
# to work. There's like a million incoherent se answers about this, and this
# is the best I got out of them.

# I cannot for the life of me figure out a sensible way of getting this included
# in a bdist without just literally embedding the directory under the package.
# thus, a symlink. Kind of ugly.
if not os.path.exists('lamb/notebooks/'):
    os.symlink(os.path.join(here, 'notebooks/'),
               os.path.join(here, 'lamb/notebooks'), target_is_directory=True)

setup_args['package_data'] = {'lamb': [
    'notebooks/*.ipynb',
    'notebooks/documentation/*.ipynb',
    'notebooks/tutorials/*.ipynb',
    'notebooks/fragments/*.ipynb',
    'notebooks/misc/*.ipynb']}
# TODO: can't get excluding Untitled.ipynb to work

# construct a kernelspect to install and include it in data_files.
# based on how `ipykernel` does this
if any(a.startswith(('bdist', 'install')) for a in sys.argv):
    sys.path.insert(0, here)
    import lamb.lnsetup

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
