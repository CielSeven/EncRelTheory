CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

MONAD_FLAG = -R $(SETS_DIR) SetsClass -R $(FIXPOINT_DIR) FP -R $(AUXLIB_DIR) AUXLib -R . MonadLib 

DEP_FLAG = -R $(SETS_DIR) SetsClass -R $(FIXPOINT_DIR) FP -R $(AUXLIB_DIR) AUXLib -R . MonadLib 

SetMonad_Files = \
	Monad.v SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v monadesafe_lib.v StateRelMonadErr.v

MonadExample_FILES = \
	kmp.v mergesort.v 
  
MONAD_FILES = \
	MonadLib.v \
	$(SetMonad_Files:%.v=SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=MonadErr/%.v) \
	$(MonadExample_FILES:%.v=Examples/%.v) \

FILES = $(MONAD_FILES)

$(MONAD_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(MONAD_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob */*.vos */*.vok */.*.aux

.DEFAULT_GOAL := all

-include .depend

