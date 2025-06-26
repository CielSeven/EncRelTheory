CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	AuxiFun auxlibs compcert_lib SeparationLogic sets unifysl StrategyLib fixedpoints
 
COQ_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R AuxiFun SimpleC.ASRTFUN -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib

DEP_FLAG = -R SeparationLogic SimpleC.SL -R unifysl Logic -R AuxiFun SimpleC.ASRTFUN -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v relations.v \
  OrdersDecFact.v BinaryTree.v 

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

AuxiFun_FILES = \
  list_lemma.v

Unify_FILES = \
   Interface.v 

SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ListLib.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v \
  IntLib.v ArrayLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v

StrategyLib_FILES = \
  DepList.v Mapping.v

Examples_FILES = \
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

	
Auto_Examples_FILES = \
	sll_shape_lib.v sll_auto_goal.v sll_auto_goal_check.v sll_auto_proof_auto.v sll_auto_proof_manual.v \

EXAMPLE = \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(MonadNrm_Files:%.v=MonadLib/monadnrm/%.v) \
	$(MonadError_Files:%.v=MonadLib/monaderror/%.v) \
	$(Examples_FILES:%.v=examples/%.v) \
	$(StrategyProof_FILES:%.v=examples/%.v) \
	$(Auto_Examples_FILES:%.v=examples/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(AuxiFun_FILES:%.v=AuxiFun/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \

AUXFILES = \

$(EXAMPLE:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
	$(EXAMPLE:%.v=%.vo) \

examples : \
	$(EXAMPLE:%.v=%.vo) 

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(EXAMPLE)  > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(EXAMPLE) > .depend

clean:
	@rm -f $(EXAMPLE:%.v=%.glob)
	@rm -f $(EXAMPLE:%.v=%.vo)
	@rm -f $(EXAMPLE:%.v=%.vok)
	@rm -f $(EXAMPLE:%.v=%.vos)
	@rm -f **/.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

include .depend