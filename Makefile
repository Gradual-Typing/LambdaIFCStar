AGD = /usr/bin/env agda

all: proofs exe
.PHONY : all

proofs: src/Proofs.agda
	$(info Checking all proofs ...)
	$(AGD) $<

exe: src/RunDemo.agda
	$(info Compiling demo programs ...)
	$(AGD) --compile --compile-dir=bin $<

.PHONY: clean
clean:
	rm -rf _build/ bin/
