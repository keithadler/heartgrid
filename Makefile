# HeartGrid - common tasks.   `make help` lists them.
PORT ?= 8755

.PHONY: help play test proofs levels solver clean

help:            ## list the tasks
	@grep -E '^[a-z]+:.*##' $(MAKEFILE_LIST) | sed 's/:.*##/ -/'

play:            ## serve the game at http://localhost:$(PORT)
	python3 -m http.server $(PORT) --directory web

test:            ## fast checks: curriculum data, and Python-vs-browser rule agreement
	python3 -m unittest discover tests

proofs:          ## check every Lean proof (about a minute)
	lake build

solver: tools/solve   ## compile the C++ solver
tools/solve: tools/solve.cpp
	clang++ -O2 -std=c++17 -o $@ $<

levels: solver   ## regenerate candidate rooms, then rebuild levels.json, the Lean files and web/levels.js
	@echo "Generating candidates (several minutes) - see tools/generate_rooms.py for the slot parameters"
	python3 tools/generate_all.py
	python3 tools/build_levels.py

clean:           ## remove build products
	rm -rf .lake tools/solve tools/__pycache__ tests/__pycache__
