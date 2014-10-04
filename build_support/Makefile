# note on spaces: must escape any spaces in variable names.  Then, use of 
# variable name later should _not_ be quoted.

# must agree with setup.py
CONTAINED_APP_NAME=start_notebook.app

APP_NAME=Lambda\ Notebook
ICON_FILE=lambdax_alpha.icns

# must agree with build_venv.sh
VENV_NAME=lambda_notebook_venv

LNVERSION=master

build_tmp:
	mkdir build_tmp

# TODO: extract at least some of this script to the makefile
$(VENV_NAME):
	./build_venv.sh

# build a self-contained virtualenv for running the lambda notebook.
env: $(VENV_NAME)

clean_env:
	rm -rf $(VENV_NAME)

clean_ln_install: 
	rm -rf $(VENV_NAME)/lambda-notebook-$(LNVERSION)/

$(VENV_NAME)/lambda-notebook-$(LNVERSION): $(VENV_NAME)
	curl -L -o build_tmp/lambdanb-distribution.zip https://github.com/rawlins/lambda-notebook/archive/$(LNVERSION).zip
	unzip -d $(VENV_NAME) build_tmp/lambdanb-distribution.zip
	ln -sfTr ./$(VENV_NAME)/lambda-notebook-$(LNVERSION)/lamb/ ./$(VENV_NAME)/lib/python3.3/site-packages/lamb
	ln -sfr $(VENV_NAME)/lambda-notebook-$(LNVERSION)/lambda_notebook.py $(VENV_NAME)/bin
	ln -sfTr $(VENV_NAME)/lambda-notebook-$(LNVERSION) $(VENV_NAME)/lambda-notebook 

lninstall: $(VENV_NAME)/lambda-notebook-$(LNVERSION)

lninstall_force: clean_ln_install lninstall

/usr/local/bin/platypus:
	@echo Error: To build the app, please install the platypus command line tool: http://www.sveinbjorn.org/platypus
	@false

# build a self-contained packaged version of the lambda notebook.  Note that this app is _not_ straightforwardly runnable by clicking, as it will have no GUI and appear frozen to the OS.
# slightly confusingly, this uses the repo version of start_notebook.py, not the downloaded one.
dist/$(CONTAINED_APP_NAME): $(VENV_NAME) setup.py start_notebook.py $(VENV_NAME)/lambda-notebook-$(LNVERSION)
	. $(VENV_NAME)/bin/activate; python setup.py py2app --packages IPython,lamb
	cp -R ./$(VENV_NAME)/lambda-notebook-$(LNVERSION)/notebooks ./dist/$(CONTAINED_APP_NAME)/Contents/Resources/package_notebooks

#build a platypus-based app wrapped around start_notebook.app
$(APP_NAME).app: /usr/local/bin/platypus dist/$(CONTAINED_APP_NAME) start_notebook_simple.sh $(ICON_FILE)
	/usr/local/bin/platypus -y -i $(ICON_FILE)  -a $(APP_NAME)  -o 'Text Window' -p '/bin/sh'  -V '0.5' -f dist/$(CONTAINED_APP_NAME) 'start_notebook_simple.sh'


clean_apps:
	rm -rf dist/$(CONTAINED_APP_NAME) $(APP_NAME).app

clean_app: clean_apps

clean_support:
	rm -rf build_tmp build dist

inner_app: dist/$(CONTAINED_APP_NAME)

# this is the main target for the platypus app
app: $(APP_NAME).app

app_master: LNVERSION = master
app_master: clean_ln_install app

$(APP_NAME).dmg: build_tmp $(APP_NAME).app README_packaged.txt
	mkdir -p build_tmp/dmg_tmp/
	cp README_packaged.txt build_tmp/dmg_tmp/README.txt
	ditto $(APP_NAME).app build_tmp/dmg_tmp/$(APP_NAME).app
	hdiutil create -fs HFSX -layout SPUD -size 100m "build_tmp/ln_tmp.dmg" -srcfolder build_tmp/dmg_tmp/ -format UDRW -volname $(APP_NAME)
	hdiutil convert "build_tmp/ln_tmp.dmg" -format UDZO -imagekey zlib-level=9 -o $(APP_NAME).dmg

dmg: $(APP_NAME).dmg

clean_dmg:
	rm -rf build_tmp/dmg_tmp/
	rm -f $(APP_NAME).dmg

install_local: app
	ditto $(APP_NAME).app ../$(APP_NAME).app

all: app dmg install_local

clean: clean_dmg clean_apps clean_support clean_env

