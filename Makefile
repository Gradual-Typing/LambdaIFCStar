AGD = /usr/bin/env agda

all: proofs demo sim
.PHONY : all

proofs: src/Proofs.agda
	$(info Checking all proofs ...)
	$(AGD) $<

demo: src/RunDemo.agda
	$(info Compiling demo programs ...)
	$(AGD) --compile --compile-dir=bin $<

sim: src/RunSimulation.agda
	$(info Compiling the simulator ...)
	$(AGD) --compile --compile-dir=bin $<

.PHONY: clean
clean:
	rm -rf _build/ bin/
