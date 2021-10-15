.PHONY: build b
build b:
	dune build

.PHONY: watch w
watch w:
	dune build --watch

.PHONY: clean
clean:
	dune clean

.PHONY: test t
test t:
	dune runtest

.PHONY: init
init:
	opam switch create . 4.12.0
	opam install . -y --deps-only
