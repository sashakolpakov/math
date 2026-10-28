import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpNodeContextSemantics

namespace OAI.Algorithms

/-! Readback of the actual layout, node initialization, and scratch-clear
outputs for the moment worker. The context masters are conclusions. -/

namespace SubexponentialSAT.SubexpMainMomentData

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def store {er es : ℕ} (alloc : Allocation es) (b : MainState er es) :
    SubexpNodeWorkspace.Store :=
  SubexpMainMomentReady.workerStacks alloc (SubexpMainNodeScratch.result alloc b)

def target (p D : ℕ) [Fact p.Prime] : SubexpSelectedConversions.Prepared p D :=
  SubexpPreparedQuarticSetup.preparedData p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

section Frames

variable {er es D : ℕ} {alloc : Allocation es} {a b : MainState er es}

theorem scratch_word (i : Fin 288) (hi : i ≠ 243) :
    store alloc b i = b.stacks (SubexpMainMomentPorts.stackMap alloc (i.castAdd 64)) := by
  apply SubexpMainNodeScratch.result_frame
  intro he
  have hm : SubexpMainMomentPorts.stackMap alloc (243 : Fin 352) = ordinary alloc 243 := rfl
  have hlocal := SubexpMainMomentPorts.stackMap_injective alloc (he.trans hm.symm)
  exact hi (Fin.ext (congrArg (fun j : Fin 352 => j.val) hlocal))

theorem initialized_word
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 288) (hi : i ≠ 243) :
    store alloc b i = SubexpNodeWideInitialization.resultStacks
      (SubexpMainNodeInitialization.projected alloc (SubexpMainNodeSetup.prepared alloc a))
      D (i.castAdd 64) :=
  (scratch_word i hi).trans (h.words (i.castAdd 64))

theorem initialized_frame
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 288) (hi : i.val ∉ ([25, 92, 109, 122, 123, 124, 125, 127, 243] : List ℕ)) :
    store alloc b i = (SubexpMainNodeSetup.prepared alloc a).stacks
      (SubexpMainMomentPorts.stackMap alloc (i.castAdd 64)) := by
  have ne (j : Fin 352)
      (hj : j.val ∈ ([25, 92, 109, 122, 123, 124, 125, 127, 243] : List ℕ)) :
      i.castAdd 64 ≠ j := by
    intro he
    have hv : i.val = j.val := congrArg (fun k : Fin 352 => k.val) he
    exact hi (hv.symm ▸ hj)
  have h243 : i ≠ 243 := by
    intro he
    subst i
    exact hi (by decide)
  exact (scratch_word i h243).trans (SubexpMainMomentReady.initializer_frame h (i.castAdd 64)
    (ne 25 (by decide)) (ne 92 (by decide)) (ne 109 (by decide))
    (ne 122 (by decide)) (ne 123 (by decide)) (ne 124 (by decide))
    (ne 125 (by decide)) (ne 127 (by decide)))

theorem prepared_retained (i : Fin 672)
    (hi : (128 ≤ i.val ∧ i.val ≤ 137) ∨ i.val = 255 ∨ i.val = 300) :
    (SubexpMainNodeSetup.prepared alloc a).stacks (ordinary alloc i) =
      a.stacks (ordinary alloc i) := by
  rw [SubexpMainNodeSetup.prepared_frame alloc a (ordinary alloc i)]
  · apply SubexpMainNodePreclear.result_frame
    change ¬ SubexpMainNodePreclear.Selected i.val
    dsimp [SubexpMainNodePreclear.Selected]
    omega
  · intro he
    have hv : i.val = 91 := congrArg (fun j : Fin (totalStacks es) => j.val) he
    omega
  · intro he
    have hv : i.val = 319 := congrArg (fun j : Fin (totalStacks es) => j.val) he
    omega
  · intro j he
    have hv := congrArg (fun k : Fin (totalStacks es) => k.val) he
    fin_cases j <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary] at hv <;> omega

theorem source_frame
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 10) :
    store alloc b ⟨128 + i.val, by omega⟩ =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  have hf := initialized_frame h (⟨128 + i.val, by omega⟩ : Fin 288) (by
    change 128 + i.val ∉ ([25, 92, 109, 122, 123, 124, 125, 127, 243] : List ℕ)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have := i.isLt
    omega)
  have hm : SubexpMainMomentPorts.stackMap alloc
      ((⟨128 + i.val, by omega⟩ : Fin 288).castAdd 64) =
      ordinary alloc ⟨128 + i.val, by omega⟩ := by
    exact SubexpMainMomentPorts.stackMap_native alloc
      ⟨128 + i.val, by omega⟩ (by intro he; have := congrArg Fin.val he; dsimp at this; omega)
      (by intro he; have := congrArg Fin.val he; dsimp at this; omega)
  rw [hm] at hf
  exact hf.trans (prepared_retained (⟨128 + i.val, by omega⟩ : Fin 672)
    (Or.inl ⟨by dsimp; omega, by dsimp; have := i.isLt; omega⟩))

theorem row_frame
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D) :
    store alloc b 255 = a.stacks (ordinary alloc 255) := by
  exact (initialized_frame h 255 (by decide)).trans
    (prepared_retained 255 (by decide))

theorem static_frame
    (h : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)
    (i : Fin 32) :
    store alloc b ⟨256 + i.val, by omega⟩ = a.stacks (master alloc i) := by
  have hf := initialized_frame h (⟨256 + i.val, by omega⟩ : Fin 288) (by
    change 256 + i.val ∉ ([25, 92, 109, 122, 123, 124, 125, 127, 243] : List ℕ)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega)
  have hm : SubexpMainMomentPorts.stackMap alloc
      ((⟨256 + i.val, by omega⟩ : Fin 288).castAdd 64) = master alloc i :=
    SubexpMainMomentPorts.stackMap_static alloc i
  rw [hm] at hf
  exact hf.trans (SubexpMainNodeSetup.prepared_master alloc a i)

theorem row_preparation_nodes (alloc : Allocation es) (a : MainState er es) :
    (SubexpMainRowPreparation.result alloc a).stacks (ordinary alloc 300) =
      a.stacks (ordinary alloc 300) := by
  have hw := alloc.enough.trans alloc.within
  change (SubexpMainRowHeader.installed alloc
    (SubexpMainRowSetup.contextResult alloc (SubexpMainRowPreparation.pre alloc a))).stacks
      (ordinary alloc 300) = _
  rw [SubexpMainRowHeader.installed_frame alloc _ (ordinary alloc 300)]
  · rw [SubexpMainRowSetup.context_high_frame alloc _ (ordinary alloc 300)
      (by change 250 ≤ 300; decide) (by change 300 < workStacks es; omega)]
    exact SubexpMainRowPreclear.result_high_frame alloc a _ (by change 288 ≤ 300; decide)
  · intro i he
    have hv := congrArg (fun j : Fin (totalStacks es) => j.val) he
    fin_cases i <;> norm_num [SubexpMainRowHeader.targetPort, ordinary] at hv
  · intro he
    have hv : (319 : ℕ) = 300 := congrArg (fun j : Fin (totalStacks es) => j.val) he
    omega

end Frames

section Layout

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
  {hregs : 16 ≤ er} {alloc : Allocation es}
  {a middle out b : MainState er es} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle out p r Δ R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc out) b D)

include h in
theorem layout_target (i : Fin 6) :
    out.stacks (persistent es (SubexpMainPreparedRings.targetIndex i)) =
      SubexpPreparedRingStaging.bankWords p D
        (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
        (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) i :=
  (SubexpMainLayoutInvariant.after_cache_words _ _ _ _ h.rows _).trans (h.rows.cache.target i)

theorem layout_source (i : Fin 10) :
    out.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      h.rows.afterLagrange.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) :=
  SubexpMainRows.Result.source_frame _ _ _ _ _ _ _ _ h.rows.rows i

include h in
theorem layout_dimension : out.stacks (master alloc 8) = List.replicate D true :=
  (SubexpMainLayoutRows.Result.master_frame _ _ _ _ h.rows 8 (by decide)).trans
    (h.choices.prefixResult.headers 3)

include h hi in
theorem target_modulus : store alloc b 5 = (target p D).modulus.bits := by
  have hf := initialized_frame hi 5 (by decide)
  change store alloc b 5 = (SubexpMainNodeSetup.prepared alloc out).stacks (persistent es 12) at hf
  exact hf.trans ((SubexpMainNodeSetup.prepared_persistent alloc out 12).trans (layout_target h 0))

include h hi in
theorem target_width : (store alloc b 10).length = baseWidth p (D + 1) := by
  have hf := initialized_frame hi 10 (by decide)
  change store alloc b 10 = (SubexpMainNodeSetup.prepared alloc out).stacks (persistent es 13) at hf
  have he := hf.trans ((SubexpMainNodeSetup.prepared_persistent alloc out 13).trans (layout_target h 1))
  exact (congrArg List.length he).trans (SubexpPreparedQuarticPrelude.widthWord_length p (D + 1))

include h hi in
theorem target_zero : store alloc b 119 = SubexpQuarticFlatMul.flat (target p D).zero := by
  have hf := initialized_frame hi 119 (by decide)
  have hh := SubexpMainNodeSetup.prepared_header alloc out 0
  exact hf.trans (hh.trans ((layout_target h 3).trans (SubexpMainRowCache.setup_flat_eq_flat _)))

include h hi in
theorem target_one : store alloc b 120 = SubexpQuarticFlatMul.flat (target p D).one := by
  have hf := initialized_frame hi 120 (by decide)
  have hh := SubexpMainNodeSetup.prepared_header alloc out 1
  exact hf.trans (hh.trans ((layout_target h 4).trans (SubexpMainRowCache.setup_flat_eq_flat _)))

include h hi in
theorem target_minusOne : store alloc b 121 = (SubexpPreparedQuarticSetup.minusOne p (D + 1)).val := by
  have hf := initialized_frame hi 121 (by decide)
  exact hf.trans ((SubexpMainNodeSetup.prepared_header alloc out 2).trans (layout_target h 5))

omit [Fact p.Prime] [NeZero r] in
include hi in
theorem index_word : store alloc b 92 = List.replicate (SubexpSymbolicCost.indexBits D) true := by
  have hw := initialized_word hi 92 (by decide)
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, Function.update_apply] using hw

omit [Fact p.Prime] [NeZero r] in
include hi in
theorem index_width : (store alloc b 92).length = SubexpSymbolicCost.indexBits D := by
  rw [index_word hi, List.length_replicate]

include h hi in
theorem dimension : store alloc b 109 = List.replicate D true := by
  have hw := initialized_word hi 109 (by decide)
  have hd := (SubexpMainNodeInitialization.projected_dimension alloc
    (SubexpMainNodeSetup.prepared alloc out)).trans
      ((SubexpMainNodeSetup.prepared_master alloc out 8).trans (layout_dimension h))
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult, hd] using hw

omit [Fact p.Prime] [NeZero r] in
include hi in
theorem raw_zero : store alloc b 122 = [false] := by
  have hw := initialized_word hi 122 (by decide)
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, Function.update_apply] using hw

include h hi in
theorem raw_one : store alloc b 123 =
    SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticFlatMul.flat (target p D).one) := by
  have hw := initialized_word hi 123 (by decide)
  have ho := (SubexpMainNodeSetup.prepared_header alloc out 1).trans
    ((layout_target h 4).trans (SubexpMainRowCache.setup_flat_eq_flat _))
  change (SubexpMainNodeInitialization.projected alloc
    (SubexpMainNodeSetup.prepared alloc out)).stacks 120 =
      SubexpQuarticFlatMul.flat (target p D).one at ho
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult, ho] using hw

include h hi in
theorem unit_word : store alloc b 124 = fixedBits (baseWidth p (D + 1)) 1 := by
  have hw := initialized_word hi 124 (by decide)
  have hp := (SubexpMainNodeInitialization.projected_width alloc
    (SubexpMainNodeSetup.prepared alloc out)).trans
      ((SubexpMainNodeSetup.prepared_persistent alloc out 13).trans (layout_target h 1))
  have hwidth := (congrArg List.length hp).trans
    (SubexpPreparedQuarticPrelude.widthWord_length p (D + 1))
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult, hwidth] using hw

include hi in
/-- The native moment context is read from actual producer results. -/
theorem context_masters : SubexpNodeContextSemantics.Masters (store alloc b)
    h.rows.cacheFacts.source (target p D) (SubexpPreparedQuarticSetup.minusOne p (D + 1)) := by
  constructor
  · exact (source_frame hi 0).trans ((layout_source h 0).trans h.rows.cacheFacts.modulus)
  · exact (source_frame hi 2).trans ((layout_source h 2).trans h.rows.cacheFacts.reduction)
  · exact (source_frame hi 3).trans ((layout_source h 3).trans
      (h.rows.cacheFacts.zero.trans (SubexpMainRowCache.flat_eq_encode _).symm))
  · exact (congrArg List.length ((source_frame hi 1).trans (layout_source h 1))).trans
      h.rows.cacheFacts.width
  · exact target_width h hi
  · exact target_modulus h hi
  · exact target_minusOne h hi
  · exact unit_word h hi

include hi in
theorem row_table : store alloc b 255 = SubexpDenseRowTableProgram.tableCode
    (SubexpDenseRowProducer.render (D + 1) h.rows.cacheFacts.source
      (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
      h.rows.cacheFacts.difference h.choices.packing.packing scopes hd) D scopes :=
  (row_frame hi).trans h.rows.rows.output

omit [Fact p.Prime] [NeZero r] in
include hi in
theorem nodes_from_layout : store alloc b 125 = out.stacks (ordinary alloc 300) := by
  have hw := initialized_word hi 125 (by decide)
  have hp := prepared_retained (alloc := alloc) (a := out) 300 (by decide)
  change (SubexpMainNodeInitialization.projected alloc
    (SubexpMainNodeSetup.prepared alloc out)).stacks 332 = out.stacks (ordinary alloc 300) at hp
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, SubexpNodeWideInitialization.dimensionResult, hp] using hw

include h in
theorem layout_nodes : out.stacks (ordinary alloc 300) = ProgramEncoding.encodeRecords
    (SubexpNodeLiftData.liftedNodeWords p (D + 1) (SubexpPreparedQuarticSetup.modulus p 1)) := by
  have hwork := alloc.enough.trans alloc.within
  have hr := h.rows.rows.externalFrame (ordinary alloc 300) (by change 288 ≤ 300; decide)
  have hp := row_preparation_nodes alloc h.rows.afterLagrange
  have hl := h.rows.lagrange.work_frame (ordinary alloc 300)
    (by change 300 < workStacks es; omega) (Or.inl (by change 300 < 320; decide))
    (by change 300 ≠ 668; decide)
  exact hr.trans (hp.trans (hl.trans h.rows.cache.lifted))

include h hi in
theorem nodes : store alloc b 125 = ProgramEncoding.encodeRecords
    (SubexpNodeLiftData.liftedNodeWords p (D + 1) (SubexpPreparedQuarticSetup.modulus p 1)) :=
  (nodes_from_layout hi).trans (layout_nodes h)

end Layout

end SubexponentialSAT.SubexpMainMomentData

end OAI.Algorithms
