build_tmp:
	mkdir build_tmp

lambda_notebook_venv: build_tmp
	./build_venv.sh

# build a self-contained virtualenv for running the lambda notebook.
env: lambda_notebook_venv

clean_env:
	rm -rf lambda_notebook_venv

# build a self-contained packaged version of the lambda notebook.  Note that this app is _not_ straightforwardly runnable by clicking, as it will have no GUI and appear frozen to the OS.
dist/start_notebook.app: lambda_notebook_venv setup.py
	. lambda_notebook_venv/bin/activate; python setup.py py2app --packages IPython,lamb

#build a platypus-based app wrapped around start_notebook.app
Lambda\ Notebook.app: /usr/local/bin/platypus dist/start_notebook.app start_notebook_simple.sh lambdax_alpha.icns
	/usr/local/bin/platypus  -i 'lambdax_alpha.icns'  -a 'Lambda Notebook'  -o 'Text Window' -p '/bin/sh'  -V '0.5' -f 'dist/start_notebook.app' 'start_notebook_simple.sh'

clean_apps:
	rm -rf dist/start_notebook.app Lambda\ Notebook.app

clean_support:
	rm -rf build_tmp build dist

# this is the main target for the platypus app
app: Lambda\ Notebook.app

clean: clean_apps clean_support clean_env

