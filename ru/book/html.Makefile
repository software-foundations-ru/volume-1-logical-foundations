EXTRA_DIR:=common
COQDOCFLAGS:= \
	--external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
	--external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
	--index indexpage \
	--no-lib-name \
	--toc \
	--with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v)
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ))
VS_OTHER := $(VS)
else
VS := $(VS_IN_PROJ)
endif

all: html

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp -r $(EXTRA_DIR)/* html
	# cp -r $/*.html html
	node -e "fs.readdirSync('./html').forEach(f => { if(/^LF\./.test(f)) { fs.renameSync('html/' + f, 'html/' + f.replace('LF\.', '')) }})" // Remove LF in html file names.

$(COQMAKEFILE): $(COQ_PROJ) $(VS)
	coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: html clean all force
