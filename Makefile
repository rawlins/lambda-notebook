.PHONY: clear demo testnb test unittest release
testopts = "--ExecutePreprocessor.timeout=120"

FORCE:

clear:
	for nb in notebooks/*.ipynb; do jupyter nbconvert --ClearOutputPreprocessor.enabled=True --inplace "$$nb" || exit 1; done
	for nb in notebooks/documentation/*.ipynb; do jupyter nbconvert --ClearOutputPreprocessor.enabled=True --inplace "$$nb" || exit 1; done
	for nb in notebooks/fragments/*.ipynb; do jupyter nbconvert --ClearOutputPreprocessor.enabled=True --inplace "$$nb" || exit 1; done
	for nb in notebooks/misc/*.ipynb; do jupyter nbconvert --ClearOutputPreprocessor.enabled=True --inplace "$$nb" || exit 1; done
	for nb in notebooks/tutorials/*.ipynb; do jupyter nbconvert --ClearOutputPreprocessor.enabled=True --inplace "$$nb" || exit 1; done

notebooks/Lambda\ Notebook\ Demo\ \(executed\).ipynb: notebooks/Lambda\ Notebook\ Demo.ipynb
	cp notebooks/Lambda\ Notebook\ Demo.ipynb notebooks/Lambda\ Notebook\ Demo\ \(executed\).ipynb
	jupyter nbconvert --execute --inplace --to notebook notebooks/Lambda\ Notebook\ Demo\ \(executed\).ipynb
	
demo: notebooks/Lambda\ Notebook\ Demo\ \(executed\).ipynb

release: clear demo

testnb:
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
