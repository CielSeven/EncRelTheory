CURRENT_DIR=.
QCP_DIR = QCP/SeparationLogic/

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Examples Language auxlib EncRelSeq compcert_lib sets unifysl fixedpoints monadlib 
 
COQ_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib -R $(QCP_DIR)SeparationLogic SimpleC.SL -R $(QCP_DIR)examples SimpleC.EE
 
DEP_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib -R $(QCP_DIR)SeparationLogic SimpleC.SL -R $(QCP_DIR)examples SimpleC.EE

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v 

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v ListLib.v OrdersDecFact.v BinaryTree.v GraphLib.v ListLibNat.v

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v 

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

Basics_FILES = \
	basictacs.v basicasrt.v semantics.v hoarelogic.v \
	relasrt.v relhoarelogic.v encdefs.v safeexec_lib.v encrel.v smallstep2deno.v enc_rules.v \

UBErrorHandling_FILES = \
	errsem.v hoarelogic.v relhoarelogic.v safeexec_lib.v encrel.v smallstep2deno.v enc_rules.v 

Functioncall_FILES = \
	callsem.v contexthoare.v contexthoare_imp.v enc_contexthoare.v enc_contexthoareimp.v 

AbsSep_FILES = \
	sepRel.v

AbsMonad_FILES = \
	relhoarelogic.v encrel.v encimpmonad.v \
	
AbsMonadE_FILES = \
	relhoarelogic.v encrel.v encimpmonadE.v \

EncRelSeq_FILES = \
	$(Basics_FILES:%.v=Basics/%.v) \
	$(UBErrorHandling_FILES:%.v=UBError/%.v) \
	$(Functioncall_FILES:%.v=Functioncall/%.v) \
	$(AbsMonad_FILES:%.v=MonadsAsHigh/AbsMonad/%.v) \
	$(AbsMonadE_FILES:%.v=MonadsAsHigh/AbsMonadE/%.v) \

Unify_FILES = \
   Interface2.v 

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
	ImpP/Mem.v ImpP/PermissionModel.v ImpP/mem_lib.v ImpP/Imp.v \
	ImpP/Seplogicrules.v  ImpP/Assertion.v ImpP/ImpTactics.v  ImpP/ImpHoareTactics.v ImpP/ImpEHoareTactics.v \
	ImpP/slllib.v ImpP/ArrayLib.v ImpP/bst_lib.v ImpP/GraphAdjList.v

Examples_FILES = \
  	impexample/Cmergesort.v impexample/CmergesortProof.v \
	impexample/CmergesortArray.v \
	impEexample/Ckmp.v  impEexample/CkmpProof.v \
	impexample/CBSTInsert.v monadexample/bst.v  impexample/CBSTInsProof.v \
	impexample/CGraphDFS.v monadexample/dfs.v monadexample/dfsproof.v impexample/CGraphDFSProof.v

VC_code_FILE_NAME = \
	kmp_rel sll_merge_rel  

VC_lib_FILES = \
	kmp_lib.v kmp_rel_lib.v sll_merge_rel_lib.v 

VC_code_proof_FILES = \
  $(VC_code_FILE_NAME:%=VC/code_proof/%_goal.v) \
  $(VC_code_FILE_NAME:%=VC/code_proof/%_proof_auto.v) \
  $(VC_code_FILE_NAME:%=VC/code_proof/%_proof_manual.v) \
  $(VC_code_FILE_NAME:%=VC/code_proof/%_goal_check.v) \

strategy_FILE_NAME = \
	safeexec safeexecE

strategy_proof_FILES = \
	$(strategy_FILE_NAME:%=VC/strategy_proof/%_strategy_goal.v) \
	$(strategy_FILE_NAME:%=VC/strategy_proof/%_strategy_proof.v) \
	$(strategy_FILE_NAME:%=VC/strategy_proof/%_strategy_goal_check.v)

MonadExampleQCP = \
	$(VC_code_proof_FILES:%=Examples/QCPexample/%) \
	$(VC_lib_FILES:%.v=Examples/QCPexample/lib/%.v) \
	$(strategy_proof_FILES:%=Examples/QCPexample/%) \

$(strategy_FILE_NAME:%=Examples/QCPexample/VC/strategy_proof/%_strategy_goal.v) : Examples/QCPexample/VC/strategy_proof/%_strategy_goal.v: Examples/QCPexample/annotated_C/%.strategies
	@echo STRATEGIES_PROOF_GEN $*.strategies
	@$(SymExec_DIR)StrategyCheck$(SYM_SUF) --strategy-folder-path=Examples/QCPexample/VC/strategy_proof/ --input-file=Examples/QCPexample/annotated_C/$*.strategies --no-exec-info

$(VC_code_FILE_NAME:%=Examples/QCPexample/VC/code_proof/%_goal.v) : Examples/QCPexample/VC/code_proof/%_goal.v: Examples/QCPexample/annotated_C/%.c
	@echo CODE_PROOF_GEN $*.c
	@$(SymExec_DIR)symexec$(SYM_SUF) --goal-file=Examples/QCPexample/VC/code_proof/$*_goal.v --proof-auto-file=Examples/QCPexample/VC/code_proof/$*_proof_auto.v --proof-manual-file=Examples/QCPexample/VC/code_proof/$*_proof_manual.v --input-file=Examples/QCPexample/annotated_C/$*.c  -slp Examples/QCPexample/annotated_C/ Examples.QCPexample.VC.strategy_proof -slp QCP/QCP_examples/ SimpleC.EE -IQCP/QCP_examples --coq-logic-path=Examples.QCPexample --no-exec-info

example_gen : \
	$(strategy_FILE_NAME:%=Examples/QCPexample/VC/strategy_proof/%_strategy_goal.v) \
	$(VC_code_FILE_NAME:%=Examples/QCPexample/VC/code_proof/%_goal.v)


FILES = \
	$(Unify_FILES:%.v=QCP/SeparationLogic/unifysl/LogicGenerator/demo932/%.v) \
    $(Sets_FILES:%.v=QCP/SeparationLogic/sets/%.v) \
    $(Compcertlib_FILES:%.v=QCP/SeparationLogic/compcert_lib/%.v) \
    $(Auxlibs_FILES:%.v=QCP/SeparationLogic/auxlibs/%.v) \
    $(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
    $(MONAD_FILES) \
	$(EncRelSeq_FILES:%.v=EncRelSeq/%.v) \
	$(MonadExampleQCP) \
	$(Language_FILES:%.v=Language/%.v) \
	$(Examples_FILES:%.v=Examples/%.v) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v



sets: $(Sets_FILES:%.v=QCP/SeparationLogic/sets/%.vo)
	@echo "====== sets built ======"


fixpoints: $(FIXPOINT_FILES:%.v=fixedpoints/%.vo)
	@echo "====== fixedpoints built ======"

enctheory: $(EncRelSeq_FILES:%.v=EncRelSeq/%.vo)
	@echo "====== enctheory built ======"

monads: $(MONAD_FILES:%.v=%.vo)
	@echo "====== monadlib built ======"

examples: $(Examples_FILES:%.v=Examples/%.vo)

language: $(Language_FILES:%.v=Language/%.vo)


all: \
  example_gen \
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