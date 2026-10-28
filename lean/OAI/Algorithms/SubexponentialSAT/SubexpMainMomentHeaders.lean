import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentData
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProduct

namespace OAI.Algorithms

/-! The remaining node-worker headers are read from the actual row,
copy, initialization, and scratch-clear results. In particular, the
radius is decoded from the retained binary input, not supplied as a
replacement unary word. -/

namespace SubexponentialSAT.SubexpMainMomentHeaders

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)
open SubexpMainMomentData (store target)
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem rawLiteral_fixed (p D : ℕ) (v : SubexpSymbolicCost.QuarticCode p D) :
    SubexpScalarLiteralProgram.rawLiteral D (SubexpQuarticFlatMul.flat v) =
      SubexpDenseSerialization.encodeFixedQuarticCoefficients p D
        [(SubexpArgumentCode.constantIndex D 0 0, v)] := by
  rw [SubexpDenseProgram.Product.flat_eq_block]
  rfl

section Initialization

variable {er es D : ℕ} {alloc : Allocation es} {a b : MainState er es}
  (hi : SubexpMainNodeInitialization.Result alloc (SubexpMainNodeSetup.prepared alloc a) b D)

include hi in
theorem moment_records :
    store alloc b 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D) := by
  have hw := SubexpMainMomentData.initialized_word hi 127 (by decide)
  simpa [SubexpNodeWideInitialization.resultStacks, SubexpNodeWideSetup.resultStacks,
    SubexpNodeWideSetup.localResult, Function.update_apply] using hw

include hi in
theorem slots :
    store alloc b 25 =
      SubexpDenseProgram.Projection.queryBytes (SubexpQueryOrder.visitSlots D) := by
  have hw := SubexpMainMomentData.initialized_word hi 25 (by decide)
  have hcast : Fin.castAdd 64 (25 : Fin 288) = (25 : Fin 352) := by
    apply Fin.ext
    rfl
  rw [hcast] at hw
  simpa only [SubexpNodeWideInitialization.resultStacks, Function.update_self,
    SubexpSlotSetup.output, SubexpSlotProgram.slots_eq_visitSlots,
    SubexpDenseProgram.Projection.queryBytes] using hw

include hi in
theorem radius_copied : store alloc b 126 = a.stacks (ordinary alloc 243) :=
  (SubexpMainMomentData.initialized_frame hi 126 (by decide)).trans
    (SubexpMainNodeSetup.prepared_header alloc a 3)

include hi in
theorem raw_zero (p : ℕ) :
    letI : Zero (SymbolicCost.CoeffList D (SubexpSymbolicCost.QuarticCode p D)) := ⟨[]⟩
    store alloc b 122 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 0 :=
  SubexpMainMomentData.raw_zero hi

end Initialization

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
theorem row_radius_value :
    out.stacks (ordinary alloc 243) =
      List.replicate (CounterPrograms.value (a.stacks (persistent es 25)) + 1) true := by
  have hf := h.rows.rows.nativeFrame 243 (by decide) (by decide) (by decide) (by decide)
  have hp := (h.rows.lagrange.persistent 25).trans
    ((h.rows.cache.persistent_frame 25 (by decide)).trans (h.choices.prefixResult.persistent 25))
  have hd := SubexpSourceRowContext.result_dimension
    (SubexpMainRowContext.input alloc h.rows.afterLagrange)
  rw [SubexpSourceRowContext.dimension, SubexpMainRowContext.input_radius, hp] at hd
  exact hf.trans ((SubexpMainRowContext.store_low alloc h.rows.afterLagrange 243
    (by decide)).trans hd)

include h hi in
theorem radius_value :
    store alloc b 126 =
      List.replicate (CounterPrograms.value (a.stacks (persistent es 25)) + 1) true :=
  (radius_copied hi).trans (row_radius_value h)

include h hi in
theorem radius (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    store alloc b 126 = List.replicate (R + 1) true := by
  rw [radius_value h hi, hRw]

include h hi in
theorem target_reduction :
    store alloc b 91 = SubexpQuarticFlatMul.flat (target p D).reduction := by
  have hf := SubexpMainMomentData.initialized_frame hi 91 (by decide)
  have hr := SubexpMainNodeReduction.installed_target alloc (SubexpMainNodeSetup.headed alloc out)
  have hp := (SubexpMainNodeReduction.installed_persistent alloc
    (SubexpMainNodeSetup.headed alloc out) 14).symm.trans
      (SubexpMainNodeSetup.prepared_persistent alloc out 14)
  exact hf.trans (hr.trans (hp.trans ((SubexpMainMomentData.layout_target h 2).trans
    (SubexpMainRowCache.setup_flat_eq_flat _))))

include h hi in
theorem raw_one :
    letI : One (SubexpSymbolicCost.QuarticCode p D) := ⟨(target p D).one⟩
    letI : One (SymbolicCost.CoeffList D (SubexpSymbolicCost.QuarticCode p D)) :=
      ⟨SubexpAlgorithm.rawOne D⟩
    store alloc b 123 = SubexpDenseSerialization.encodeFixedQuarticCoefficients p D 1 := by
  rw [SubexpMainMomentData.raw_one h hi]
  exact rawLiteral_fixed p D (target p D).one

end Layout

end SubexponentialSAT.SubexpMainMomentHeaders

end OAI.Algorithms
