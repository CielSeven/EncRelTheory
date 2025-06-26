CURRENT_DIR=.
QCP_DIR = QCP/SeparationLogic/

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Examples Language auxlib EncRelSeq compcert_lib sets unifysl fixedpoints monadlib 
 
COQ_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib

DEP_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v 

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v ListLib.v OrdersDecFact.v BinaryTree.v GraphLib.v ListLibNat.v

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v 

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

AsrtLogic_FILES = \
	SLInterface1.v SLInterface2.v 

Basics_FILES = \
	basictacs.v basicasrt.v semantics.v hoarelogic.v \
	relasrt.v relhoarelogic.v encdefs.v safeexec_lib.v encrel.v smallstep2deno.v enc_rules.v \

UBErrorHandling_FILES = \
	errsem.v hoarelogic.v relhoarelogic.v safeexec_lib.v encrel.v smallstep2deno.v enc_rules.v \

Functioncall_FILES = \
	callsem.v contexthoare.v contexthoare_imp.v enc_contexthoare.v \
	# enc_contexthoareimp.v 

AbsSep_FILES = \
	sepRel.v

AbsMonad_FILES = \
	enc_rules.v encimpmonad.v encrel.v hoarelogic.v 
	
AbsMonadE_FILES = \
	encimpmonadE.v encrel.v hoarelogic.v 

EncRelSeq_FILES = \
	$(AsrtLogic_FILES:%.v=AsrtLogic/%.v) \
	$(Basics_FILES:%.v=Basics/%.v) \
	$(UBErrorHandling_FILES:%.v=UBError/%.v) \
	$(Functioncall_FILES:%.v=Functioncall/%.v) \
	# $(AbsSep_FILES:%.v=AbsSep/%.v) \
	# $(AbsMonad_FILES:%.v=AbsMonad/%.v) \
	# $(AbsMonadE_FILES:%.v=AbsMonadE/%.v) \

Unify_FILES = \
   Interface.v 

SetMonad_Files = \
	Monad.v SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v monadesafe_lib.v StateRelMonadErr.v

MonadExample_FILES = \
	kmp.v mergesort.v 
  
MONAD_FILES = \
	monadlib/MonadLib.v \
	$(SetMonad_Files:%.v=monadlib/SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=monadlib/StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=monadlib/MonadErr/%.v) \
	$(MonadExample_FILES:%.v=monadlib/Examples/%.v) \


Language_FILES = \
	ImpP/Mem.v ImpP/PermissionModel.v ImpP/mem_lib.v ImpP/Imp.v ImpP/Assertion.v ImpP/ImpTactics.v  ImpP/ImpHoareTactics.v ImpP/ImpEHoareTactics.v \
	ImpP/slllib.v ImpP/ArrayLib.v ImpP/bst_lib.v ImpP/GraphAdjList.v

Examples_FILES = \
  	impexample/Cmergesort.v impexample/CmergesortProof.v \
	impexample/CmergesortArray.v \
	impEexample/Ckmp.v  impEexample/CkmpProof.v \
	impexample/CBSTInsert.v monadexample/bst.v  impexample/CBSTInsProof.v \
	impexample/CGraphDFS.v monadexample/dfs.v monadexample/dfsproof.v impexample/CGraphDFSProof.v


FILES = \
    $(Sets_FILES:%.v=QCP/SeparationLogic/sets/%.v) \
    $(Compcertlib_FILES:%.v=QCP/SeparationLogic/compcert_lib/%.v) \
    $(Auxlibs_FILES:%.v=QCP/SeparationLogic/auxlibs/%.v) \
    $(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
    $(MONAD_FILES) \
    $(EncRelSeq_FILES:%.v=EncRelSeq/%.v) \
# 	$(Language_FILES:%.v=Language/%.v) \
# 	$(Examples_FILES:%.v=Examples/%.v) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo) \

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean: 
	@rm -f $(FILES:%.v=%.glob)  
	@rm -f $(FILES:%.v=%.vo)  
	@rm -f $(FILES:%.v=%.vok)  
	@rm -f $(FILES:%.v=%.vos)  
	@rm -f $(FILES:%.v=.%.aux)  
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

include .depend