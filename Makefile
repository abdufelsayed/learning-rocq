ROCQ ?= rocq

PROJECT_FILE := _CoqProject
SOURCE_DIR := src
VFILES := $(sort $(wildcard $(SOURCE_DIR)/*.v))
GENERATED_FILES := Makefile.coq Makefile.coq.conf .filestoinstall .Makefile.coq.d

.PHONY: all build clean

all: build

build: Makefile.coq
	$(MAKE) -f $<

Makefile.coq: $(PROJECT_FILE) $(VFILES)
	$(ROCQ) makefile -f $(PROJECT_FILE) -o $@ $(VFILES)

clean::
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(GENERATED_FILES)

-include Makefile.coq
