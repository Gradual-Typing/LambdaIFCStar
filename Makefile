%.agdai: %.agda
	/usr/bin/env agda  $<

AGDA = Compile.agda TypeSafety.agda BigStepErasedDeterministic.agda Noninterference.agda Examples.agda

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
