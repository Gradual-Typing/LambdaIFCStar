%.agdai: %.agda
	/usr/bin/env agda  $<

AGDA = Compile.agda TypeSafety.agda Noninterference.agda

AGDAI = $(AGDA:%.agda=%.agdai)

all: ${AGDA} ${AGDAI}

clean:
	rm -f *.agdai *~
