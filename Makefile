# Makefile to build everything

build:
	python3 -m pip install --upgrade pip
	python3 -m pip install --upgrade build
	python3 -m build

install:
	test `ls ./dist/atomkraft-informal-*.tar.gz | wc -l` -lt 2 \
		|| (echo "Found multiple distributions in ./dist"; exit 1)
	python3 -m pip install ./dist/atomkraft-informal-*.*.*.tar.gz

test: ./tests
	# extend PYTHONPATH to include our module
	PYTHONPATH="./src:${PYTHONPATH}" \
		python -m unittest discover -s src -s tests -p 'test_*.py'

clean:
	rm -rf ./dist
