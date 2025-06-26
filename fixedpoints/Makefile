CURRENT_DIR=.
SETS_DIR = ../sets

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

FP_FLAG = -Q $(CURRENT_DIR) FP -R $(SETS_DIR) SetsClass
SETS_FLAG = -R $(SETS_DIR) SetsClass

DEP_FLAG = -Q $(CURRENT_DIR) FP -R $(SETS_DIR) SetsClass

FP_FILES_NAMES = \
  AllFramework.v \
  Coqlib.v \
  LiftConstructors.v \
  PartialOrder_Setoid.v \
  KnasterTarski.v \
  BourbakiWitt.v \
  SetsFixedpoints.v

FP_FILES=$(FP_FILES_NAMES:%.v=$(CURRENT_DIR)/%.v)

FILES = $(FP_FILES)

$(FP_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FP_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vos *.vok

.DEFAULT_GOAL := all

-include .depend

