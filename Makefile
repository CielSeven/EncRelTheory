CURRENT_DIR=.
QCP_DIR = QCP/SeparationLogic/

COQBIN=        # Path to your Coq binaries, or leave empty if 'coqc' is in your PATH
SymExec_DIR=   # Set to QCP/win-binary/ on Windows, QCP/linux-binary/ on Linux, or QCP/mac-arm64-binary/ on MacOS
SYM_SUF=       # Set to .exe on Windows; leave empty on Linux and MacOS
SUF=           # Set to .exe on Windows; leave empty on Linux and MacOS

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Examples Language auxlib EncRelSeq compcert_lib sets unifysl fixedpoints monadlib 
 
COQ_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib -R $(QCP_DIR)SeparationLogic SimpleC.SL -R $(QCP_DIR)examples SimpleC.EE -R $(QCP_DIR)StrategyLib SimpleC.StrategyLib
 
DEP_FLAG = -R $(QCP_DIR)sets SetsClass -R $(QCP_DIR)unifysl Logic -R $(QCP_DIR)compcert_lib compcert.lib -R $(QCP_DIR)auxlibs AUXLib -R EncRelSeq EncRelSeq -R Language LangLib -R Examples Examples -R fixedpoints FP -R monadlib MonadLib -R $(QCP_DIR)SeparationLogic SimpleC.SL -R $(QCP_DIR)examples SimpleC.EE -R $(QCP_DIR)StrategyLib SimpleC.StrategyLib

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v 

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v ListLib.v OrdersDecFact.v BinaryTree.v GraphLib.v ListLibNat.v relations.v 

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
	SetBasic.v SetHoare.v FixpointLib.v SetMonad.v

StateRelMonad_Files = \
	StateRelBasic.v StateRelHoare.v FixpointLib.v safeexec_lib.v StateRelMonad.v

MonadErr_Files = \
	MonadErrBasic.v MonadErrLoop.v MonadErrHoare.v monadesafe_lib.v StateRelMonadErr.v

OptionMonad_Files = \
	OptionBasic.v OptionMonad.v

ListMonad_Files = \
	ListBasic.v ListMonad.v

MonadExample_FILES = \
	kmp.v mergesort.v 
  
MONAD_FILES = \
	monadlib/Monad.v \
	monadlib/MonadLib.v \
	$(SetMonad_Files:%.v=monadlib/SetMonad/%.v) \
	$(StateRelMonad_Files:%.v=monadlib/StateRelMonad/%.v) \
	$(MonadErr_Files:%.v=monadlib/MonadErr/%.v) \
	$(OptionMonad_Files:%.v=monadlib/OptionMonad/%.v) \
	$(ListMonad_Files:%.v=monadlib/ListMonad/%.v) \
	$(MonadExample_FILES:%.v=monadlib/Examples/%.v) \


Language_FILES = \
	ImpP/Mem.v ImpP/PermissionModel.v ImpP/mem_lib.v ImpP/Imp.v \
	ImpP/Seplogicrules.v ImpP/Assertion.v ImpP/ImpTactics.v  ImpP/ImpHoareTactics.v ImpP/ImpEHoareTactics.v \
	ImpP/slllib.v ImpP/ArrayLib.v ImpP/bst_lib.v ImpP/GraphAdjList.v

Examples_FILES = \
  	impexample/Cmergesort.v impexample/CmergesortProof.v \
	impEexample/Ckmp.v  impEexample/CkmpProof.v \
	impexample/CBSTInsert.v monadexample/bst.v  impexample/CBSTInsProof.v \
	impexample/CGraphDFS.v monadexample/dfs.v monadexample/dfsproof.v impexample/CGraphDFSProof.v


SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v \
  IntLib.v ArrayLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v

StrategyLib_FILES = \
  DepList.v Mapping.v

Qcp_Examples_FILES = \
  poly_sll_lib.v poly_sll_goal.v poly_sll_goal_check.v poly_sll_proof_auto.v poly_sll_proof_manual.v \
  sll_lib.v sll_goal.v sll_goal_check.v sll_proof_auto.v sll_proof_manual.v \
  sll_merge_lib.v sll_merge_goal.v sll_merge_goal_check.v sll_merge_proof_auto.v sll_merge_proof_manual.v \
	sll_insert_sort_lib.v sll_insert_sort_goal.v sll_insert_sort_goal_check.v sll_insert_sort_proof_auto.v sll_insert_sort_proof_manual.v \
	functional_queue_lib.v functional_queue_goal.v functional_queue_goal_check.v functional_queue_proof_auto.v functional_queue_proof_manual.v \
	dll_queue_lib.v dll_queue_goal.v dll_queue_goal_check.v dll_queue_proof_auto.v dll_queue_proof_manual.v \
	sll_queue_lib.v sll_queue_goal.v sll_queue_goal_check.v sll_queue_proof_auto.v sll_queue_proof_manual.v \
	simple_arith/abs_goal.v simple_arith/abs_goal_check.v simple_arith/abs_proof_auto.v simple_arith/abs_proof_manual.v \
	simple_arith/add_goal.v simple_arith/add_goal_check.v simple_arith/add_proof_auto.v simple_arith/add_proof_manual.v \
	simple_arith/max3_goal.v simple_arith/max3_goal_check.v simple_arith/max3_proof_auto.v simple_arith/max3_proof_manual.v \
	simple_arith/gcd_goal.v simple_arith/gcd_goal_check.v simple_arith/gcd_proof_auto.v simple_arith/gcd_proof_manual.v \
	simple_arith/Apos_lib.v simple_arith/Always_pos_goal.v simple_arith/Always_pos_goal_check.v simple_arith/Always_pos_proof_auto.v simple_arith/Always_pos_proof_manual.v \
	simple_arith/PDiv_lib.v simple_arith/div_test_goal.v simple_arith/div_test_goal_check.v simple_arith/div_test_proof_auto.v simple_arith/div_test_proof_manual.v \
	simple_arith/exgcd_goal.v simple_arith/exgcd_goal_check.v simple_arith/exgcd_proof_auto.v simple_arith/exgcd_proof_manual.v \
	sum_goal.v sum_goal_check.v sum_proof_auto.v sum_proof_manual.v \
	bst_lib.v bst_insert_goal.v bst_insert_goal_check.v bst_insert_proof_auto.v bst_insert_proof_manual.v \
	bst_insert_rec_goal.v bst_insert_rec_goal_check.v bst_insert_rec_proof_auto.v bst_insert_rec_proof_manual.v \
	bst_fp_lib.v bst_fp_insert_goal.v bst_fp_insert_goal_check.v bst_fp_insert_proof_auto.v bst_fp_insert_proof_manual.v \
	bst_fp_delete_goal.v bst_fp_delete_goal_check.v bst_fp_delete_proof_auto.v bst_fp_delete_proof_manual.v \
	swap_lib.v swap_goal.v swap_goal_check.v swap_proof_auto.v swap_proof_manual.v \
	eval_lib.v eval_goal.v eval_goal_check.v eval_proof_auto.v eval_proof_manual.v \
	bst_delete_rec_goal.v bst_delete_rec_goal_check.v bst_delete_rec_proof_auto.v bst_delete_rec_proof_manual.v \
	bst_delete_rec2_goal.v bst_delete_rec2_goal_check.v bst_delete_rec2_proof_auto.v bst_delete_rec2_proof_manual.v \
	fme/algorithm.v fme/implement.v fme/implement_lemma.v fme/fme_lib.v fme/fme_goal.v fme/fme_goal_check.v fme/fme_proof_auto.v fme/fme_proof_manual.v \
	typeinfer/correct_impl.v typeinfer/repr_subst_prop.v typeinfer/sol_prop.v typeinfer/sound_pv.v typeinfer/type_infer_lib.v typeinfer/typeinfer_lib.v typeinfer/typeinfer_goal.v typeinfer/typeinfer_goal_check.v typeinfer/typeinfer_proof_auto.v typeinfer/typeinfer_proof_manual.v \
  
StrategyProof_FILES = \
	common_strategy_goal.v common_strategy_proof.v common_strategy_goal_check.v \
	poly_sll_strategy_goal.v poly_sll_strategy_proof.v poly_sll_strategy_goal_check.v \
	sll_shape_strategy_goal.v sll_shape_strategy_proof.v sll_shape_strategy_goal_check.v \
	sll_strategy_goal.v sll_strategy_proof.v sll_strategy_goal_check.v \
	dll_queue_strategy_goal.v dll_queue_strategy_proof.v dll_queue_strategy_goal_check.v \
	functional_queue_strategy_goal.v functional_queue_strategy_proof.v functional_queue_strategy_goal_check.v \
	sll_queue_strategy_goal.v sll_queue_strategy_proof.v sll_queue_strategy_goal_check.v \
	int_array_strategy_goal.v int_array_strategy_proof.v int_array_strategy_goal_check.v \
	bst_strategy_goal.v bst_strategy_proof.v bst_strategy_goal_check.v \
	bst_fp_strategy_goal.v bst_fp_strategy_proof.v bst_fp_strategy_goal_check.v \
	eval_strategy_goal.v eval_strategy_proof.v eval_strategy_goal_check.v \
	char_array_strategy_goal.v char_array_strategy_proof.v char_array_strategy_goal_check.v \
	fme/fme_strategy_goal.v fme/fme_strategy_proof.v fme/fme_strategy_goal_check.v \
	typeinfer/typeinfer_strategy_goal.v typeinfer/typeinfer_strategy_proof.v typeinfer/typeinfer_strategy_goal_check.v \

Qcp_Unify_FILES = \
   Interface.v 
	
Auto_Examples_FILES = \
	sll_shape_lib.v sll_auto_goal.v sll_auto_goal_check.v sll_auto_proof_auto.v sll_auto_proof_manual.v \

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

QCP_Relational_Examples = \
	$(Qcp_Unify_FILES:%.v=QCP/SeparationLogic/unifysl/LogicGenerator/demo932/%.v) \
	$(SL_FILES:%.v=QCP/SeparationLogic/SeparationLogic/%.v) \
	$(MonadExampleQCP) \


QCPFILES = \
	$(Qcp_Unify_FILES:%.v=QCP/SeparationLogic/unifysl/LogicGenerator/demo932/%.v) \
	$(SL_FILES:%.v=QCP/SeparationLogic/SeparationLogic/%.v) \
	$(Qcp_Examples_FILES:%.v=QCP/SeparationLogic/examples/%.v) \
	$(StrategyProof_FILES:%.v=QCP/SeparationLogic/examples/%.v) \
	$(Auto_Examples_FILES:%.v=QCP/SeparationLogic/examples/%.v) \
	$(MonadExampleQCP) \

$(QCPFILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v


FILES = \
	$(Unify_FILES:%.v=QCP/SeparationLogic/unifysl/LogicGenerator/demo932/%.v) \
    $(Sets_FILES:%.v=QCP/SeparationLogic/sets/%.v) \
    $(Compcertlib_FILES:%.v=QCP/SeparationLogic/compcert_lib/%.v) \
    $(Auxlibs_FILES:%.v=QCP/SeparationLogic/auxlibs/%.v) \
    $(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
    $(MONAD_FILES) \
	$(EncRelSeq_FILES:%.v=EncRelSeq/%.v) \
	$(Language_FILES:%.v=Language/%.v) \
	$(Examples_FILES:%.v=Examples/%.v) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v


TEST_VC_code_FILE_NAME = \
	test  

TEST_VC_code_proof_FILES = \
  $(TEST_VC_code_FILE_NAME:%=VC/code_proof/%_goal.v) \
  $(TEST_VC_code_FILE_NAME:%=VC/code_proof/%_proof_auto.v) \
  $(TEST_VC_code_FILE_NAME:%=VC/code_proof/%_proof_manual.v) \
  $(TEST_VC_code_FILE_NAME:%=VC/code_proof/%_goal_check.v) \

TESTExampleQCP = \
	$(TEST_VC_code_proof_FILES:%=Examples/QCPexample/%) \

$(TESTExampleQCP:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v


$(TEST_VC_code_FILE_NAME:%=Examples/QCPexample/VC/code_proof/%_goal.v) : Examples/QCPexample/VC/code_proof/%_goal.v: Examples/QCPexample/annotated_C/%.c
	@echo CODE_PROOF_GEN $*.c
	@$(SymExec_DIR)symexec$(SYM_SUF) --goal-file=Examples/QCPexample/VC/code_proof/$*_goal.v --proof-auto-file=Examples/QCPexample/VC/code_proof/$*_proof_auto.v --proof-manual-file=Examples/QCPexample/VC/code_proof/$*_proof_manual.v --input-file=Examples/QCPexample/annotated_C/$*.c  -slp Examples/QCPexample/annotated_C/ Examples.QCPexample.VC.strategy_proof -slp QCP/QCP_examples/ SimpleC.EE -IQCP/QCP_examples --coq-logic-path=Examples.QCPexample --no-exec-info


sets: $(Sets_FILES:%.v=QCP/SeparationLogic/sets/%.vo)
	@echo "====== sets built ======"


fixpoints: $(FIXPOINT_FILES:%.v=fixedpoints/%.vo)
	@echo "====== fixedpoints built ======"

enctheory: $(EncRelSeq_FILES:%.v=EncRelSeq/%.vo)
	@echo "====== enctheory built ======"

monads: $(MONAD_FILES:%.v=%.vo)
	@echo "====== monadlib built ======"

language: $(Language_FILES:%.v=Language/%.vo)
	@echo "====== monadlib built ======"

encexample: $(FILES:%.v=%.vo)
	@echo "====== enctheory demo language and examples built ======"

qcpexample:  example_gen \
  $(QCP_Relational_Examples:%.v=%.vo) 
	@echo "====== QCP examples built ======"

qcpfullexample:  example_gen \
  $(QCPFILES:%.v=%.vo) 
	@echo "====== QCP full examples built ======"

test_gen : \
	$(TEST_VC_code_FILE_NAME:%=Examples/QCPexample/VC/code_proof/%_goal.v)

checktest : test_gen \
  $(TESTExampleQCP:%.v=%.vo) 
	@echo "====== QCP test built ======"


all: \
  $(FILES:%.v=%.vo) \
  example_gen \
  $(QCP_Relational_Examples:%.v=%.vo) \

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) $(QCPFILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) $(QCPFILES) > .depend

clean: 
	@rm -f $(FILES:%.v=%.glob)  
	@rm -f $(FILES:%.v=%.vo)  
	@rm -f $(FILES:%.v=%.vok)  
	@rm -f $(FILES:%.v=%.vos)  
	@rm -f $(FILES:%.v=.%.aux)  
	@rm -f $(QCPFILES:%.v=%.glob)  
	@rm -f $(QCPFILES:%.v=%.vo)  
	@rm -f $(QCPFILES:%.v=%.vok)  
	@rm -f $(QCPFILES:%.v=%.vos)  
	@rm -f $(QCPFILES:%.v=.%.aux)  
	@rm -f **/.*.aux
	@rm -f **/**/.*.aux
	@rm -f .depend

cleantest: 
	@rm -f $(TESTExampleQCP:%.v=%.glob)  
	@rm -f $(TESTExampleQCP:%.v=%.vo)  
	@rm -f $(TESTExampleQCP:%.v=%.vok)  
	@rm -f $(TESTExampleQCP:%.v=%.vos)  
	@rm -f $(TESTExampleQCP:%.v=.%.aux)  
	@rm -f $(TESTExampleQCP)



.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend