# COMP 212 standard Makefile
#
# N. Danner

# Dependency lists.

TARGETS=driver

# ##########
# It should not be necessary to modify anything below this line.
# ##########

CMFILES=$(addsuffix .cm, $(TARGETS))
DEPS=$(shell egrep --no-filename '\.lex|\.sig|\.sml' $(CMFILES) | cut --delim=: --fields=1) $(CMFILES)

# SML/NJ programs
SML_BIN=
SML=$(SML_BIN)sml
ML_BUILD=$(SML_BIN)ml-build
H2E=/usr/local/bin/heap2exec32

# Options and additional CM files for ml-build.
ML_BUILD_OPTS=-Ctdp.instrument=true
ML_BUILD_CMS=\$$smlnj-tdp/back-trace.cm

# Compute the heap suffix.
HEAP_SUFFIX=$(shell $(SML) @SMLsuffix)

$(TARGETS) : $(DEPS)
	$(ML_BUILD) $(ML_BUILD_OPTS) $(ML_BUILD_CMS) $@.cm Main.main $@
	$(H2E) $@.$(HEAP_SUFFIX) $@
	rm $@.$(HEAP_SUFFIX)

# Cleanup targets.
clean :
	rm -rf .cm
	rm -f *.lex.sml *.grm.sml
	rm -f $(TARGETS)
	rm -f $(addsuffix .$(HEAP_SUFFIX), $(TARGETS))


