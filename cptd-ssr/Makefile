MODULES := pred prelude idynamic
RELEASE := $(MODULES:%=%.v) Makefile Makefile.build
ssr.pname := $(SSRCOQ_LIB)
ssr.lname := Ssreflect
COQLIBS := ssr

include Makefile.build

all: coq
