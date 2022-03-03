// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Init Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Rename Lean.Meta.Tactic.Intro Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_instInhabitedTerminationByElement;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__17;
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__19;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
uint8_t l_Lean_Expr_isLit(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
static lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__23;
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__21;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__16;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__20;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__14;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__18;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; 
lean_dec(x_7);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
{
size_t _tmp_3 = x_14;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_WF_instInhabitedTerminationByElement;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
x_6 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_5, x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.WF.Rel");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackMutual.go");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
x_3 = lean_unsigned_to_nat(26u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_array_push(x_5, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Cases_cases(x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_22);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
x_28 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_fget(x_22, x_29);
x_31 = lean_array_fget(x_22, x_14);
lean_dec(x_22);
x_32 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_array_get(x_36, x_35, x_29);
lean_dec(x_35);
x_38 = l_Lean_Expr_fvarId_x21(x_37);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_array_get(x_36, x_40, x_29);
lean_dec(x_40);
x_42 = l_Lean_Expr_fvarId_x21(x_41);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_5, x_44);
x_2 = x_32;
x_3 = x_34;
x_4 = x_38;
x_5 = x_45;
x_12 = x_23;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_13 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(x_1, x_11, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackUnary.go");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(50u);
x_4 = lean_unsigned_to_nat(85u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_instInhabitedName;
x_19 = l_Array_back___rarg(x_18, x_3);
lean_dec(x_3);
x_20 = l_Lean_Meta_rename(x_4, x_5, x_19, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_nat_add(x_6, x_2);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_array_get(x_22, x_3, x_21);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_29 = lean_array_push(x_28, x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Meta_Cases_cases(x_4, x_5, x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_31);
x_34 = lean_nat_dec_eq(x_33, x_15);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
x_36 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_31, x_37);
lean_dec(x_31);
x_39 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_instInhabitedExpr;
x_44 = lean_array_get(x_43, x_42, x_15);
lean_dec(x_42);
x_45 = l_Lean_Expr_fvarId_x21(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_6, x_3, x_1, x_39, x_41, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_30);
if (x_47 == 0)
{
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wf");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("i: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", varNames: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", goal: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_42 = lean_st_ref_get(x_12, x_13);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = 0;
x_15 = x_47;
x_16 = x_46;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_15 = x_52;
x_16 = x_51;
goto block_41;
}
block_41:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_4);
x_19 = l_Nat_repr(x_4);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_2);
x_26 = lean_array_to_list(lean_box(0), x_2);
x_27 = lean_box(0);
x_28 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_26, x_27);
x_29 = l_Lean_MessageData_ofList(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_5);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_14, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Lean_Expr_fvarId_x21(x_13);
lean_inc(x_6);
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = l_Lean_instInhabitedSyntax;
x_21 = lean_array_get(x_20, x_1, x_4);
x_22 = l_Lean_Syntax_isIdent(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_get_size(x_7);
x_26 = lean_nat_sub(x_25, x_2);
lean_dec(x_25);
x_27 = lean_nat_add(x_26, x_4);
lean_dec(x_26);
x_28 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
x_29 = lean_array_set(x_7, x_27, x_28);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_30;
x_7 = x_29;
goto _start;
}
}
else
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_14);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_14);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
lean_inc(x_1);
x_20 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_2);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
lean_inc(x_1);
x_38 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_5, x_48);
x_5 = x_49;
x_6 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; 
lean_inc(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_18 = x_29;
x_19 = x_12;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_18 = x_38;
x_19 = x_12;
goto block_28;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_30, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_33, x_34);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_34, x_44);
lean_dec(x_34);
lean_ctor_set(x_30, 1, x_45);
x_46 = l_Lean_LocalDecl_userName(x_31);
x_47 = lean_name_eq(x_46, x_43);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_Meta_rename(x_32, x_48, x_43, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_30);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_53;
x_19 = x_51;
goto block_28;
}
else
{
uint8_t x_54; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
lean_dec(x_31);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_32);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_18 = x_59;
x_19 = x_12;
goto block_28;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_30);
x_60 = lean_array_fget(x_33, x_34);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_34, x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_35);
x_64 = l_Lean_LocalDecl_userName(x_31);
x_65 = lean_name_eq(x_64, x_60);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_67 = l_Lean_Meta_rename(x_32, x_66, x_60, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_18 = x_71;
x_19 = x_69;
goto block_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_31);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_18 = x_77;
x_19 = x_12;
goto block_28;
}
}
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_4, x_25);
x_4 = x_26;
x_5 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_array_get_size(x_11);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_12, x_11, x_15, x_16, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_array_get_size(x_34);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_35, x_34, x_38, x_39, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_44, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_30; 
lean_inc(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_18 = x_30;
x_19 = x_12;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_18 = x_39;
x_19 = x_12;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_31, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = lean_array_fget(x_34, x_35);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_35, x_45);
lean_dec(x_35);
lean_ctor_set(x_31, 1, x_46);
x_47 = l_Lean_LocalDecl_userName(x_32);
x_48 = lean_name_eq(x_47, x_44);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_Meta_rename(x_33, x_49, x_44, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_18 = x_54;
x_19 = x_52;
goto block_29;
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_33);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_18 = x_60;
x_19 = x_12;
goto block_29;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_31);
x_61 = lean_array_fget(x_34, x_35);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_35, x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
x_65 = l_Lean_LocalDecl_userName(x_32);
x_66 = lean_name_eq(x_65, x_61);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_Meta_rename(x_33, x_67, x_61, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_18 = x_72;
x_19 = x_70;
goto block_29;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_61);
lean_dec(x_32);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_33);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_18 = x_78;
x_19 = x_12;
goto block_29;
}
}
}
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_22, x_21, x_25, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_11, x_12, x_12, x_13, x_12, x_14, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many variable names");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_6);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_15, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_15);
x_23 = l_Lean_instInhabitedSyntax;
x_24 = lean_array_get(x_23, x_18, x_17);
lean_dec(x_17);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_6);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed), 10, 1);
lean_closure_set(x_14, 0, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_getMVarDecl(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_16);
x_22 = l_Array_toSubarray___rarg(x_16, x_21, x_2);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_16);
x_31 = lean_nat_sub(x_30, x_2);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_2, x_16, x_31, x_21, x_29, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_sub(x_9, x_1);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_ctor_get(x_12, 5);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___rarg(x_15, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_14, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SizeOf");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sizeOf");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_nat_add(x_17, x_19);
lean_ctor_set(x_15, 0, x_26);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_28 = lean_array_push(x_27, x_13);
x_29 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_mkAppM(x_29, x_28, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_whnfD(x_31, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_isLit(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
size_t x_37; size_t x_38; 
lean_dec(x_17);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; 
x_40 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_40);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_9 = x_35;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_45);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_3 = x_47;
x_9 = x_44;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_50);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_9 = x_49;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
x_54 = lean_nat_add(x_17, x_19);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_18);
lean_ctor_set(x_55, 2, x_19);
x_56 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_57 = lean_array_push(x_56, x_13);
x_58 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_mkAppM(x_58, x_57, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_whnfD(x_60, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_isLit(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
size_t x_66; size_t x_67; 
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_55);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_3 = x_67;
x_9 = x_64;
goto _start;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; 
x_69 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_55);
x_70 = 1;
x_71 = lean_usize_add(x_3, x_70);
x_3 = x_71;
x_9 = x_64;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_74);
lean_ctor_set(x_4, 0, x_55);
x_75 = 1;
x_76 = lean_usize_add(x_3, x_75);
x_3 = x_76;
x_9 = x_73;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; 
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_79);
lean_ctor_set(x_4, 0, x_55);
x_80 = 1;
x_81 = lean_usize_add(x_3, x_80);
x_3 = x_81;
x_9 = x_78;
goto _start;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_4, 0);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_4);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc(x_87);
x_88 = lean_nat_dec_lt(x_85, x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_85, x_87);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
x_94 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_95 = lean_array_push(x_94, x_13);
x_96 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_97 = l_Lean_Meta_mkAppM(x_96, x_95, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_Meta_whnfD(x_98, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_isLit(x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; size_t x_105; size_t x_106; 
lean_dec(x_85);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_84);
x_105 = 1;
x_106 = lean_usize_add(x_3, x_105);
x_3 = x_106;
x_4 = x_104;
x_9 = x_102;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; 
x_108 = lean_array_push(x_84, x_85);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_108);
x_110 = 1;
x_111 = lean_usize_add(x_3, x_110);
x_3 = x_111;
x_4 = x_109;
x_9 = x_102;
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; 
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_114 = lean_array_push(x_84, x_85);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_93);
lean_ctor_set(x_115, 1, x_114);
x_116 = 1;
x_117 = lean_usize_add(x_3, x_116);
x_3 = x_117;
x_4 = x_115;
x_9 = x_113;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; 
x_119 = lean_ctor_get(x_97, 1);
lean_inc(x_119);
lean_dec(x_97);
x_120 = lean_array_push(x_84, x_85);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_93);
lean_ctor_set(x_121, 1, x_120);
x_122 = 1;
x_123 = lean_usize_add(x_3, x_122);
x_3 = x_123;
x_4 = x_121;
x_9 = x_119;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___rarg(x_2, x_1, x_13);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_14, x_18, x_20, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_4, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_nat_add(x_4, x_15);
lean_inc(x_6);
lean_inc(x_10);
x_19 = lean_array_push(x_10, x_6);
x_20 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_18, x_19, x_11);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_30 = lean_box(0);
x_5 = x_16;
x_6 = x_29;
x_9 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_33 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
x_9 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_push(x_6, x_5);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_16, x_18, x_19, x_5, x_6);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_6 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_15);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_19, x_20, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_assignExprMVar(x_1, x_22, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_16, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_16, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_22, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_33);
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_20, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_20, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_20, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_34, x_35);
x_44 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
lean_ctor_set(x_20, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_43);
lean_inc(x_1);
x_45 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_46, x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; size_t x_51; size_t x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 1;
x_52 = lean_usize_add(x_4, x_51);
x_4 = x_52;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_43);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_62 = lean_array_fget(x_34, x_35);
x_63 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
lean_inc(x_1);
x_65 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_66, x_68, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; size_t x_71; size_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_ctor_set(x_5, 1, x_64);
x_71 = 1;
x_72 = lean_usize_add(x_4, x_71);
x_4 = x_72;
x_12 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_16);
x_82 = lean_array_fget(x_22, x_23);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_23, x_83);
lean_dec(x_23);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_24);
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_20, 2);
lean_inc(x_88);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_12);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_91 = x_20;
} else {
 lean_dec_ref(x_20);
 x_91 = lean_box(0);
}
x_92 = lean_array_fget(x_86, x_87);
x_93 = lean_nat_add(x_87, x_83);
lean_dec(x_87);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_88);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_92);
lean_inc(x_1);
x_95 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_82, x_1, x_18, x_17, x_92, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_96);
x_98 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_98, 0, x_96);
lean_closure_set(x_98, 1, x_92);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_96, x_98, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; size_t x_101; size_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_ctor_set(x_5, 1, x_94);
lean_ctor_set(x_5, 0, x_85);
x_101 = 1;
x_102 = lean_usize_add(x_4, x_101);
x_4 = x_102;
x_12 = x_100;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_110 = x_95;
} else {
 lean_dec_ref(x_95);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_5, 1);
lean_inc(x_112);
lean_dec(x_5);
x_113 = lean_ctor_get(x_16, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_16, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_16, 2);
lean_inc(x_115);
x_116 = lean_nat_dec_lt(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_16);
lean_ctor_set(x_117, 1, x_112);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_12);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_119 = x_16;
} else {
 lean_dec_ref(x_16);
 x_119 = lean_box(0);
}
x_120 = lean_array_fget(x_113, x_114);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_114, x_121);
lean_dec(x_114);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_115);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_112, 2);
lean_inc(x_126);
x_127 = lean_nat_dec_lt(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_112);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_12);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_130 = x_112;
} else {
 lean_dec_ref(x_112);
 x_130 = lean_box(0);
}
x_131 = lean_array_fget(x_124, x_125);
x_132 = lean_nat_add(x_125, x_121);
lean_dec(x_125);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_126);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_131);
lean_inc(x_1);
x_134 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_120, x_1, x_18, x_17, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_135);
x_137 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_137, 0, x_135);
lean_closure_set(x_137, 1, x_131);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_138 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_135, x_137, x_6, x_7, x_8, x_9, x_10, x_11, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_133);
x_141 = 1;
x_142 = lean_usize_add(x_4, x_141);
x_4 = x_142;
x_5 = x_140;
x_12 = x_139;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invImage");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to apply 'invImage'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_11, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_11, 3, x_16);
x_17 = lean_box(0);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_17, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_22, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_26 = l_Lean_Meta_apply(x_21, x_24, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_30 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_34 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_38 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_44 = l_Lean_Meta_intro1Core(x_41, x_43, x_9, x_10, x_11, x_12, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_49 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_48, x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_array_get_size(x_4);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_toSubarray___rarg(x_4, x_53, x_52);
x_55 = lean_array_get_size(x_3);
x_56 = l_Array_toSubarray___rarg(x_3, x_53, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_array_get_size(x_50);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_50, x_59, x_60, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_50);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_42);
x_63 = l_Lean_mkMVar(x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_64 = lean_infer_type(x_63, x_9, x_10, x_11, x_12, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_68 = l_Lean_Meta_synthInstance(x_65, x_67, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_assignExprMVar(x_42, x_69, x_9, x_10, x_11, x_12, x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_mkMVar(x_21);
lean_inc(x_10);
x_74 = l_Lean_Meta_instantiateMVars(x_73, x_9, x_10, x_11, x_12, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_apply_8(x_6, x_75, x_7, x_8, x_9, x_10, x_11, x_12, x_76);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_68);
if (x_78 == 0)
{
return x_68;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_68, 0);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_68);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_64);
if (x_82 == 0)
{
return x_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_64, 0);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_64);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
return x_61;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_61, 0);
x_88 = lean_ctor_get(x_61, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_61);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_49);
if (x_90 == 0)
{
return x_49;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_49, 0);
x_92 = lean_ctor_get(x_49, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_49);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_44);
if (x_94 == 0)
{
return x_44;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_44, 0);
x_96 = lean_ctor_get(x_44, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_44);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_39);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_26, 1);
lean_inc(x_98);
lean_dec(x_26);
x_99 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_100 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_99, x_7, x_8, x_9, x_10, x_11, x_12, x_98);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_26);
if (x_101 == 0)
{
return x_26;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_26, 0);
x_103 = lean_ctor_get(x_26, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_26);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_23);
if (x_105 == 0)
{
return x_23;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_23, 0);
x_107 = lean_ctor_get(x_23, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_23);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_109 = lean_ctor_get(x_11, 0);
x_110 = lean_ctor_get(x_11, 1);
x_111 = lean_ctor_get(x_11, 2);
x_112 = lean_ctor_get(x_11, 3);
x_113 = lean_ctor_get(x_11, 4);
x_114 = lean_ctor_get(x_11, 5);
x_115 = lean_ctor_get(x_11, 6);
x_116 = lean_ctor_get(x_11, 7);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_11);
x_117 = l_Lean_replaceRef(x_1, x_112);
lean_dec(x_112);
lean_dec(x_1);
x_118 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_118, 0, x_109);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_111);
lean_ctor_set(x_118, 3, x_117);
lean_ctor_set(x_118, 4, x_113);
lean_ctor_set(x_118, 5, x_114);
lean_ctor_set(x_118, 6, x_115);
lean_ctor_set(x_118, 7, x_116);
x_119 = lean_box(0);
lean_inc(x_9);
x_120 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_119, x_9, x_10, x_118, x_12, x_13);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_Expr_mvarId_x21(x_121);
lean_dec(x_121);
x_124 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
x_125 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_124, x_9, x_10, x_118, x_12, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_123);
x_128 = l_Lean_Meta_apply(x_123, x_126, x_9, x_10, x_118, x_12, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_132 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_131, x_7, x_8, x_9, x_10, x_118, x_12, x_130);
lean_dec(x_12);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_132;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_136 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_135, x_7, x_8, x_9, x_10, x_118, x_12, x_134);
lean_dec(x_12);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
lean_dec(x_128);
x_139 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_140 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_139, x_7, x_8, x_9, x_10, x_118, x_12, x_138);
lean_dec(x_12);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_140;
}
else
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_128, 1);
lean_inc(x_142);
lean_dec(x_128);
x_143 = lean_ctor_get(x_129, 0);
lean_inc(x_143);
lean_dec(x_129);
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
x_145 = 0;
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
x_146 = l_Lean_Meta_intro1Core(x_143, x_145, x_9, x_10, x_118, x_12, x_142);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_151 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_150, x_149, x_7, x_8, x_9, x_10, x_118, x_12, x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_array_get_size(x_4);
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Array_toSubarray___rarg(x_4, x_155, x_154);
x_157 = lean_array_get_size(x_3);
x_158 = l_Array_toSubarray___rarg(x_3, x_155, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
x_160 = lean_array_get_size(x_152);
x_161 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_162 = 0;
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_163 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_152, x_161, x_162, x_159, x_7, x_8, x_9, x_10, x_118, x_12, x_153);
lean_dec(x_152);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
lean_inc(x_144);
x_165 = l_Lean_mkMVar(x_144);
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
x_166 = lean_infer_type(x_165, x_9, x_10, x_118, x_12, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(0);
lean_inc(x_12);
lean_inc(x_118);
lean_inc(x_10);
lean_inc(x_9);
x_170 = l_Lean_Meta_synthInstance(x_167, x_169, x_9, x_10, x_118, x_12, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_assignExprMVar(x_144, x_171, x_9, x_10, x_118, x_12, x_172);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_mkMVar(x_123);
lean_inc(x_10);
x_176 = l_Lean_Meta_instantiateMVars(x_175, x_9, x_10, x_118, x_12, x_174);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_apply_8(x_6, x_177, x_7, x_8, x_9, x_10, x_118, x_12, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_144);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_180 = lean_ctor_get(x_170, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_182 = x_170;
} else {
 lean_dec_ref(x_170);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_144);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_184 = lean_ctor_get(x_166, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_166, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_186 = x_166;
} else {
 lean_dec_ref(x_166);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_144);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_188 = lean_ctor_get(x_163, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_163, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_190 = x_163;
} else {
 lean_dec_ref(x_163);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_144);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_192 = lean_ctor_get(x_151, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_151, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_194 = x_151;
} else {
 lean_dec_ref(x_151);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_144);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_ctor_get(x_146, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_146, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_198 = x_146;
} else {
 lean_dec_ref(x_146);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_141);
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_ctor_get(x_128, 1);
lean_inc(x_200);
lean_dec(x_128);
x_201 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_202 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_201, x_7, x_8, x_9, x_10, x_118, x_12, x_200);
lean_dec(x_12);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_202;
}
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_ctor_get(x_128, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_128, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_205 = x_128;
} else {
 lean_dec_ref(x_128);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_207 = lean_ctor_get(x_125, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_125, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_209 = x_125;
} else {
 lean_dec_ref(x_125);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1), 13, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
x_16 = l_Lean_Elab_Term_withDeclName___rarg(x_2, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
lean_inc(x_1);
x_19 = lean_array_push(x_6, x_1);
x_20 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_18;
x_3 = x_20;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_8, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_22, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_22, 0);
lean_dec(x_33);
x_34 = lean_array_fget(x_25, x_26);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_26, x_35);
lean_dec(x_26);
lean_ctor_set(x_22, 1, x_36);
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 2);
lean_inc(x_39);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_15);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_43 = lean_ctor_get(x_23, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_23, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_23, 0);
lean_dec(x_45);
x_46 = lean_array_fget(x_37, x_38);
x_47 = lean_nat_add(x_38, x_35);
lean_dec(x_38);
lean_ctor_set(x_23, 1, x_47);
lean_inc(x_1);
lean_inc(x_2);
x_48 = lean_array_push(x_2, x_1);
x_49 = lean_nat_sub(x_46, x_34);
lean_dec(x_34);
lean_dec(x_46);
x_50 = lean_nat_sub(x_49, x_35);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(0u);
lean_inc(x_50);
lean_inc(x_4);
x_52 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_4, x_50, x_51, x_50, x_35, x_48, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_18, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_18, 3);
lean_inc(x_56);
lean_dec(x_18);
x_57 = 0;
lean_inc(x_3);
x_58 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_3);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = lean_array_push(x_24, x_58);
lean_ctor_set(x_20, 1, x_59);
x_60 = 1;
x_61 = lean_usize_add(x_7, x_60);
x_7 = x_61;
x_15 = x_54;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; 
lean_dec(x_23);
x_63 = lean_array_fget(x_37, x_38);
x_64 = lean_nat_add(x_38, x_35);
lean_dec(x_38);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_39);
lean_inc(x_1);
lean_inc(x_2);
x_66 = lean_array_push(x_2, x_1);
x_67 = lean_nat_sub(x_63, x_34);
lean_dec(x_34);
lean_dec(x_63);
x_68 = lean_nat_sub(x_67, x_35);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(0u);
lean_inc(x_68);
lean_inc(x_4);
x_70 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_4, x_68, x_69, x_68, x_35, x_66, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_18, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_18, 3);
lean_inc(x_74);
lean_dec(x_18);
x_75 = 0;
lean_inc(x_3);
x_76 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_3);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
x_77 = lean_array_push(x_24, x_76);
lean_ctor_set(x_20, 1, x_77);
lean_ctor_set(x_20, 0, x_65);
x_78 = 1;
x_79 = lean_usize_add(x_7, x_78);
x_7 = x_79;
x_15 = x_72;
goto _start;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_22);
x_81 = lean_array_fget(x_25, x_26);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_26, x_82);
lean_dec(x_26);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_25);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_27);
x_85 = lean_ctor_get(x_23, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_23, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_23, 2);
lean_inc(x_87);
x_88 = lean_nat_dec_lt(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_84);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_8);
lean_ctor_set(x_89, 1, x_15);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_90 = x_23;
} else {
 lean_dec_ref(x_23);
 x_90 = lean_box(0);
}
x_91 = lean_array_fget(x_85, x_86);
x_92 = lean_nat_add(x_86, x_82);
lean_dec(x_86);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_87);
lean_inc(x_1);
lean_inc(x_2);
x_94 = lean_array_push(x_2, x_1);
x_95 = lean_nat_sub(x_91, x_81);
lean_dec(x_81);
lean_dec(x_91);
x_96 = lean_nat_sub(x_95, x_82);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(0u);
lean_inc(x_96);
lean_inc(x_4);
x_98 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_4, x_96, x_97, x_96, x_82, x_94, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_18, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_18, 3);
lean_inc(x_102);
lean_dec(x_18);
x_103 = 0;
lean_inc(x_3);
x_104 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_3);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
x_105 = lean_array_push(x_24, x_104);
lean_ctor_set(x_20, 1, x_105);
lean_ctor_set(x_20, 0, x_93);
lean_ctor_set(x_8, 0, x_84);
x_106 = 1;
x_107 = lean_usize_add(x_7, x_106);
x_7 = x_107;
x_15 = x_100;
goto _start;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_8, 0);
x_110 = lean_ctor_get(x_20, 0);
x_111 = lean_ctor_get(x_20, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_20);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
x_115 = lean_nat_dec_lt(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_8, 1, x_116);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_8);
lean_ctor_set(x_117, 1, x_15);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
x_119 = lean_array_fget(x_112, x_113);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_add(x_113, x_120);
lean_dec(x_113);
if (lean_is_scalar(x_118)) {
 x_122 = lean_alloc_ctor(0, 3, 0);
} else {
 x_122 = x_118;
}
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_114);
x_123 = lean_ctor_get(x_110, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_110, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_110, 2);
lean_inc(x_125);
x_126 = lean_nat_dec_lt(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_119);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_110);
lean_ctor_set(x_127, 1, x_111);
lean_ctor_set(x_8, 1, x_127);
lean_ctor_set(x_8, 0, x_122);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_8);
lean_ctor_set(x_128, 1, x_15);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; size_t x_147; 
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 x_129 = x_110;
} else {
 lean_dec_ref(x_110);
 x_129 = lean_box(0);
}
x_130 = lean_array_fget(x_123, x_124);
x_131 = lean_nat_add(x_124, x_120);
lean_dec(x_124);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_125);
lean_inc(x_1);
lean_inc(x_2);
x_133 = lean_array_push(x_2, x_1);
x_134 = lean_nat_sub(x_130, x_119);
lean_dec(x_119);
lean_dec(x_130);
x_135 = lean_nat_sub(x_134, x_120);
lean_dec(x_134);
x_136 = lean_unsigned_to_nat(0u);
lean_inc(x_135);
lean_inc(x_4);
x_137 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_4, x_135, x_136, x_135, x_120, x_133, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_18, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_18, 3);
lean_inc(x_141);
lean_dec(x_18);
x_142 = 0;
lean_inc(x_3);
x_143 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_138);
lean_ctor_set(x_143, 3, x_3);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_142);
x_144 = lean_array_push(x_111, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_132);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_8, 1, x_145);
lean_ctor_set(x_8, 0, x_122);
x_146 = 1;
x_147 = lean_usize_add(x_7, x_146);
x_7 = x_147;
x_15 = x_139;
goto _start;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_149 = lean_ctor_get(x_8, 1);
x_150 = lean_ctor_get(x_8, 0);
lean_inc(x_149);
lean_inc(x_150);
lean_dec(x_8);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_150, 2);
lean_inc(x_156);
x_157 = lean_nat_dec_lt(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_153)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_153;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_150);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_15);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 x_161 = x_150;
} else {
 lean_dec_ref(x_150);
 x_161 = lean_box(0);
}
x_162 = lean_array_fget(x_154, x_155);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_nat_add(x_155, x_163);
lean_dec(x_155);
if (lean_is_scalar(x_161)) {
 x_165 = lean_alloc_ctor(0, 3, 0);
} else {
 x_165 = x_161;
}
lean_ctor_set(x_165, 0, x_154);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_156);
x_166 = lean_ctor_get(x_151, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_151, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_151, 2);
lean_inc(x_168);
x_169 = lean_nat_dec_lt(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_153)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_153;
}
lean_ctor_set(x_170, 0, x_151);
lean_ctor_set(x_170, 1, x_152);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_15);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; size_t x_191; size_t x_192; 
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 x_173 = x_151;
} else {
 lean_dec_ref(x_151);
 x_173 = lean_box(0);
}
x_174 = lean_array_fget(x_166, x_167);
x_175 = lean_nat_add(x_167, x_163);
lean_dec(x_167);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_168);
lean_inc(x_1);
lean_inc(x_2);
x_177 = lean_array_push(x_2, x_1);
x_178 = lean_nat_sub(x_174, x_162);
lean_dec(x_162);
lean_dec(x_174);
x_179 = lean_nat_sub(x_178, x_163);
lean_dec(x_178);
x_180 = lean_unsigned_to_nat(0u);
lean_inc(x_179);
lean_inc(x_4);
x_181 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_4, x_179, x_180, x_179, x_163, x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_179);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_18, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_18, 3);
lean_inc(x_185);
lean_dec(x_18);
x_186 = 0;
lean_inc(x_3);
x_187 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_187, 2, x_182);
lean_ctor_set(x_187, 3, x_3);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_186);
x_188 = lean_array_push(x_152, x_187);
if (lean_is_scalar(x_153)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_153;
}
lean_ctor_set(x_189, 0, x_176);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_165);
lean_ctor_set(x_190, 1, x_189);
x_191 = 1;
x_192 = lean_usize_add(x_7, x_191);
x_7 = x_192;
x_8 = x_190;
x_15 = x_183;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc(x_8);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
x_21 = l_Lean_addMacroScope(x_18, x_20, x_15);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_inc(x_8);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__15;
lean_inc(x_29);
lean_inc(x_32);
x_35 = l_Lean_addMacroScope(x_32, x_34, x_29);
x_36 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__14;
x_37 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__17;
lean_inc(x_26);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Lean_addMacroScope(x_32, x_20, x_29);
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_23);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_22);
x_41 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_42 = lean_array_push(x_41, x_40);
x_43 = lean_box(2);
x_44 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__19;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
x_46 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__20;
x_47 = lean_array_push(x_46, x_38);
x_48 = lean_array_push(x_47, x_45);
x_49 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
lean_inc(x_8);
x_51 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_33);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__23;
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_41, x_59);
x_61 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__22;
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_array_get_size(x_2);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Array_toSubarray___rarg(x_2, x_64, x_63);
x_66 = lean_array_get_size(x_3);
x_67 = l_Array_toSubarray___rarg(x_3, x_64, x_66);
x_68 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_array_get_size(x_1);
x_72 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_73 = 0;
x_74 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_24, x_41, x_50, x_62, x_1, x_72, x_73, x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_8);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 0;
x_22 = l_Lean_Elab_Term_SavedState_restore(x_10, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Elab_Term_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 0;
x_27 = l_Lean_Elab_Term_SavedState_restore(x_15, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_10, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_21 = lean_array_uget(x_8, x_10);
lean_inc(x_16);
lean_inc(x_6);
x_22 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_6, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = lean_usize_add(x_10, x_28);
lean_inc(x_7);
{
size_t _tmp_9 = x_29;
lean_object* _tmp_10 = x_7;
lean_object* _tmp_17 = x_27;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_18 = _tmp_17;
}
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_42 = x_26;
} else {
 lean_dec_ref(x_26);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed), 18, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to prove termination, use `termination_by` to specify a well-founded relation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_13 = l_Lean_Elab_WF_getNumCandidateArgs(x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_3, x_17, x_18, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
x_23 = lean_unsigned_to_nat(32u);
x_24 = l_Lean_Elab_WF_generateCombinations_x3f(x_20, x_14, x_23);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_14, x_28, x_25, x_27, x_18, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = lean_apply_8(x_22, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
x_16 = l_Lean_Meta_instantiateMVars(x_14, x_6, x_7, x_8, x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_17);
x_19 = l_Lean_Meta_getMVars(x_17, x_6, x_7, x_8, x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_20, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_8(x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel_guess___rarg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_1, 0, x_6);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_box(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_5);
x_25 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_1);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_6);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_box(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_35, 0, x_29);
lean_closure_set(x_35, 1, x_30);
lean_closure_set(x_35, 2, x_33);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_31);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_31);
lean_closure_set(x_36, 2, x_5);
x_37 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WellFoundedRelation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabWFRel start: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_Meta_getLevel(x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkApp(x_20, x_4);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_43 = lean_st_ref_get(x_12, x_16);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_23 = x_48;
x_24 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_23 = x_53;
x_24 = x_52;
goto block_42;
}
block_42:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = 0;
x_28 = lean_box(0);
lean_inc(x_9);
x_29 = l_Lean_Meta_mkFreshTypeMVar(x_27, x_28, x_9, x_10, x_11, x_12, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_22, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_39);
return x_41;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1);
l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4);
l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1 = _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__1);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__2);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__3);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__4);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__5 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__5);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__6 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__6);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__7 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__7);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__8 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__8);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__9 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__9);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__10 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__10);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__11 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__11);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__12 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__12);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__13 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__13);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__14 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__14();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__14);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__15 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__15();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__15);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__16 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__16();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__16);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__17 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__17();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__17);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__18 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__18();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__18);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__19 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__19();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__19);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__20 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__20();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__20);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__21 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__21();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__21);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__22 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__22();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__22);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__23 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__23();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__23);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___closed__2 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___closed__3 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__3);
l_Lean_Elab_WF_elabWFRel___rarg___closed__4 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
