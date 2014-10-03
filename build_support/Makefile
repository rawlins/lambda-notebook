build_tmp:
	mkdir build_tmp

lambda_notebook_venv: build_tmp
	./build_venv.sh

# build a self-contained virtualenv for running the lambda notebook.
env: lambda_notebook_venv

clean_env:
	rm -rf lambda_notebook_venv

# build a self-contained packaged version of the lambda notebook.  Note that this app is _not_ straightforwardly runnable by clicking, as it will have no GUI and appear frozen to the OS.
dist/start_notebook.app: lambda_notebook_venv setup.py start_notebook.py
	. lambda_notebook_venv/bin/activate; python setup.py py2app --packages IPython,lamb
	cp -R ./lambda_notebook_venv/lambda-notebook-master/notebooks ./dist/start_notebook.app/Contents/Resources/package_notebooks

#build a platypus-based app wrapped around start_notebook.app
Lambda\ Notebook.app: /usr/local/bin/platypus dist/start_notebook.app start_notebook_simple.sh lambdax_alpha.icns
	/usr/local/bin/platypus  -i 'lambdax_alpha.icns'  -a 'Lambda Notebook'  -o 'Text Window' -p '/bin/sh'  -V '0.5' -f 'dist/start_notebook.app' 'start_notebook_simple.sh'

clean_apps:
	rm -rf dist/start_notebook.app Lambda\ Notebook.app

clean_support:
	rm -rf build_tmp build dist

# this is the main target for the platypus app
app: Lambda\ Notebook.app

Lambda\ Notebook.dmg: build_tmp Lambda\ Notebook.app README_packaged.txt
	mkdir -p build_tmp/dmg_tmp/
	cp README_packaged.txt build_tmp/dmg_tmp/README.txt
	ditto Lambda\ Notebook.app build_tmp/dmg_tmp/Lambda\ Notebook.app
	hdiutil create -fs HFSX -layout SPUD -size 100m "build_tmp/ln_tmp.dmg" -srcfolder build_tmp/dmg_tmp/ -format UDRW -volname "Lambda Notebook"
	hdiutil convert "build_tmp/ln_tmp.dmg" -format UDZO -imagekey zlib-level=9 -o "Lambda Notebook.dmg"

dmg: Lambda\ Notebook.dmg

clean_dmg:
	rm -rf build_tmp/dmg_tmp/
	rm -f "Lambda Notebook.dmg"

clean: clean_apps clean_support clean_env clean_dmg

