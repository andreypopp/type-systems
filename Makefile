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
