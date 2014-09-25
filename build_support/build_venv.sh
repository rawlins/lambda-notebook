#!/bin/sh
# script to build a clean virtual environment preloaded with the current master for the lambda notebook, and dependencies.
# note that this doesn't use the local version.

# Assumes that easy_install is installed, for python 3.3, and in the path.

# this is originally based on a script by Marc Liyanage, as part of an ipython app bundle: https://github.com/liyanage/ipython-notebook
# I (KR) needed to strip out a lot of stuff that wasn't working and wasn't necessary.  For example, the original script built a bunch of computer vision stuff.

# TODO: this currently doesn't load the full scipy stack, since numpy seems to break py2app right now (9/2014).  Revisit this.  Not crucial but it would be nice to have the stack built in.
# TODO: revisit the matplotlib issue.  Liyanage's script built freetype and libpng as part of an xcode build, and packaged them in.  Right now I just leave this out.
# TODO: refactor into a Makefile or something

set -e
set -x


# added for testing purposes, remove if used in xcode
export STARTING_DIR=`pwd`
export DERIVED_FILE_DIR=`pwd`/build_tmp/
export CONFIGURATION_TEMP_DIR=`pwd`

# This is a temporary directory to install the base tools that
# we need to build the virtualenv. It is not the virtualenv itself
# and it is not included in the final product.
BUILD_PYTHONPATH="$DERIVED_FILE_DIR"/build-python-lib
export PYTHONPATH="$BUILD_PYTHONPATH"
export PATH="$BUILD_PYTHONPATH":"$PATH"
mkdir -p "$BUILD_PYTHONPATH"



# We need pip and virtualenv to build the virtualenv
if ! pip freeze >/dev/null 2>&1; then
    echo Installing pip...
    easy_install-3.3 --install-dir="$BUILD_PYTHONPATH" pip
fi


if ! type virtualenv >/dev/null 2>&1; then
    echo Installing virtualenv...
    easy_install-3.3 --install-dir="$BUILD_PYTHONPATH" virtualenv
    VIRTUALENV="$BUILD_PYTHONPATH"/virtualenv
else
    VIRTUALENV=virtualenv
fi


VIRTUALENV_DIR="`pwd`/lambda_notebook_venv/"
rm -rf "$VIRTUALENV_DIR"
mkdir -p "$VIRTUALENV_DIR"

cd "$VIRTUALENV_DIR"

# Initialize the virtualenv
if ! [ -e .Python ]; then
    "$VIRTUALENV" --no-site-packages .
fi

if [[ ! -e "$VIRTUALENV_DIR"/bin/pandoc ]]; then
    PANDOC_DISTRIBUTION="$DERIVED_FILE_DIR"/pandoc
    mkdir -p "$PANDOC_DISTRIBUTION"
    pushd "$PANDOC_DISTRIBUTION"
    curl -L -o "$DERIVED_FILE_DIR"/pandoc.dmg https://pandoc.googlecode.com/files/pandoc-1.12.1-1.dmg
    mountpoint=$(hdiutil attach "$DERIVED_FILE_DIR"/pandoc.dmg -nobrowse -noautoopen -plist | grep -A1 mount-point | grep string | sed -E 's/\<[^\>]+\>//g')
    mountpoint=$(echo $mountpoint) # Remove whitespace
    echo "$image mounted at $mountpoint"
    gunzip -c "$mountpoint/pandoc-"*.pkg/Contents/Archive.pax.gz | pax -r
    echo "Unmounting $image"
    hdiutil detach "$mountpoint"
    popd
    cp "$PANDOC_DISTRIBUTION"/usr/local/bin/pandoc "$VIRTUALENV_DIR"/bin/
    #rm -rf "$PANDOC_DISTRIBUTION"
    #rm pandoc.dmg
fi

# Activate the virtualenv and then use pip to install various
# required modules that we want to include.
. bin/activate

export CC=clang
export CXX=clang
#export FFLAGS=-ff2c

# Install modules - unit testing
pip install nose


#if ! pip install scipy > "$CONFIGURATION_TEMP_DIR"/install-scipy.log; then
#    echo scipy installation failed:
#    cat "$CONFIGURATION_TEMP_DIR"/install-scipy.log
#    exit 1
#fi

# TODO: return once other things are sorted out
# Install modules - matplotlib
# CFLAGS="-I$SCRIPT_INPUT_FILE_1/include -I$SCRIPT_INPUT_FILE_2/include/freetype2 -I$SCRIPT_INPUT_FILE_2/include"
# LDFLAGS="-framework ApplicationServices -L$SCRIPT_INPUT_FILE_1/lib -L$SCRIPT_INPUT_FILE_2/lib"
# CFLAGS="$CFLAGS" LDFLAGS="$LDFLAGS" pip install matplotlib

# this is currently the best way to go
pip install ipython[all]

#pip install pandas
#nosetests pandas


# Download and embed MathJax, so that the app doesn't
# have to load it from the CDN at runtime.

# KR: currently not doing this because this is a big download with a _massive_ number of files, really makes the app folder annoying to deal with
# python <<EOF
# from IPython.external.mathjax import install_mathjax
# # KR: n.b. the default for 'tag' is wrong in ipython 2.1, this will be fixed in future version.  Right now specify directly.
# install_mathjax(tag="2.4.0", dest="$VIRTUALENV_DIR/lib/python3.3/site-packages/IPython/html/static/mathjax")
# EOF

curl -L -o "$DERIVED_FILE_DIR"/lambdanb-distribution.zip https://github.com/rawlins/lambda-notebook/archive/master.zip
unzip -d "$VIRTUALENV_DIR" "$DERIVED_FILE_DIR"/lambdanb-distribution.zip
ln -s "$VIRTUALENV_DIR"/lambda-notebook-master/lamb/ "$VIRTUALENV_DIR"/lib/python3.3/site-packages/lamb
ln -s "$VIRTUALENV_DIR"/lambda-notebook-master/lambda_notebook.py "$VIRTUALENV_DIR"/bin
#rm lambdanb-distribution.zip

pip install py2app
#TODO: need to not do this if this bug (in py2app) is fixed
patch "$VIRTUALENV_DIR"/lib/python3.3/site-packages/modulegraph/modulegraph.py "$STARTING_DIR"/modulegraph_fix.diff

touch "$VIRTUALENV_DIR"


