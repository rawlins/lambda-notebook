.PHONY: clear testnb test unittest release site cleardocs
testopts = "--ExecutePreprocessor.timeout=120"
clearopts = --ClearOutputPreprocessor.enabled=True

FORCE:

cleancmd = nb-clean clean

cleardocs:
	for nb in docs/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done

clear: cleardocs
	for nb in notebooks/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done
	for nb in notebooks/documentation/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done
	for nb in notebooks/fragments/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done
	for nb in notebooks/misc/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done
	for nb in notebooks/tutorials/*.ipynb; do $(cleancmd) "$$nb" || exit 1; done

# note: assumes `lamb` in pythonpath! currently satisfied by a symlink...
site:
	quarto render docs/ --execute

release: clear

testnb:
	for nb in docs/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done
	for nb in notebooks/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done
	for nb in notebooks/documentation/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done
	for nb in notebooks/fragments/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done
	for nb in notebooks/misc/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done
	for nb in notebooks/tutorials/*.ipynb; do jupyter nbconvert --execute --to notebook --stdout $(testopts) "$$nb" > /dev/null || exit 1; done

unittest:
	python3 -m unittest lamb.types
	python3 -m unittest discover

test: unittest testnb

clean:
	rm -rf dist/ data_kernelspec/ build/ lambda_notebook.egg-info/ test_env/
	rm -f lamb/notebooks

dist: FORCE
	python -m build
	@echo -e "\\nDid you remember to increment versions, set __release__=True, and tag?"

test_env:
	python -m venv test_env
	source test_env/bin/activate && pip install --upgrade pip
