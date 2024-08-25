#!/usr/bin/env python3
import os, sys

try:
    import lamb
except ImportError:
    print("The lambda notebook library can't be found; can't start a shell.")
    raise

# assume we are running in the repository filesystem; insert the script location
# into the python path so that the repository version of the package is used
# regardless of where the script is called from. (This behavior is different
# than `import -m lamb.console`)
import lamb.lnsetup
base_path = os.path.abspath(os.path.dirname(__file__))
lamb.lnsetup.launch_lambda_console(sys.argv, lib_dir=base_path)
