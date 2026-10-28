import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainSystemCRTBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentCanonicalOutput
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds

namespace OAI.Algorithms

/-!
# Actual post-moment storage for CRT

The layout program clears the CRT bank, the node preparation preserves it,
and the collector restores the decoder scratch. The remaining input-size
terms are the two retained binary words for dimension and inverse exponent.
Their lengths are bounded at the actual layout output, without counting the
pending leaf stream. The readback record supplies the exact node/jet arrays.
-/

namespace SubexponentialSAT.SubexpMainMomentCRTBounds

open scoped BigOperators
open SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)
open SubexpMainLayoutWordBounds (RelevantWordBound)

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The physical bank reserved for CRT, before its preparation runs. -/
def BankEmpty {er es : ℕ} (a : MainState er es) : Prop :=
  ∀ i, 320 ≤ i.val → i.val < 640 → a.stacks i = []

theorem row_prepared_crt_frame {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (i : Fin (totalStacks es))
    (hlo : 320 ≤ i.val) (hhi : i.val < 640) :
    (SubexpMainRowPreparation.result alloc a).stacks i = a.stacks i := by
  have hw := alloc.enough.trans alloc.within
  have ht (j : Fin 6) : SubexpMainRowHeader.targetPort alloc j ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    fin_cases j <;> norm_num [SubexpMainRowHeader.targetPort, ordinary] at hv <;> omega
  have htmp : ordinary alloc 319 ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    change 319 = i.val at hv
    omega
  rw [SubexpMainRowPreparation.result, SubexpMainRowSetup.result,
    SubexpMainRowHeader.installed_frame alloc _ i ht htmp,
    SubexpMainRowSetup.context_high_frame alloc _ i (by omega) (by omega)]
  exact SubexpMainRowPreclear.result_high_frame alloc a i (by omega)

/-- Native Lagrange scratch is cleared; holes in its allocation are framed.
This includes the native inputs and output, which live outside the bank. -/
theorem lagrange_bank_empty {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {bytes : List Bool}
    (h : SubexpMainLagrangeCache.Result alloc a b bytes) (ha : BankEmpty a) :
    BankEmpty b := by
  intro i hlo hhi
  by_cases hm : ∃ j, SubexpMainLagrangeCache.stackMap alloc j = i
  · obtain ⟨j, rfl⟩ := hm
    have hj : SubexpMainLagrangeCache.inputIndex j = none := by
      cases he : SubexpMainLagrangeCache.inputIndex j with
      | none => rfl
      | some q =>
          have hw := alloc.enough.trans alloc.within
          simp only [SubexpMainLagrangeCache.stackMap, he, persistent,
            Fin.val_natAdd] at hhi
          omega
    have h250 : j ≠ 250 := by
      intro he
      subst j
      change 668 < 640 at hhi
      omega
    exact h.scratch j hj h250
  · exact (h.frame i hm).trans (ha i hlo hhi)

section Layout

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
  {hregs : 16 ≤ er} {alloc : Allocation es}
  {a middle layoutOut : MainState er es} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ R D hr hQ scopes hd tables)

include h in
/-- All 320 words are empty after the actual choices/cache/Lagrange/row
pipeline, with no initial bank-emptiness assumption. -/
theorem layout_bank_empty : BankEmpty layoutOut := by
  have hm : BankEmpty middle := by
    intro i hlo hhi
    have he := h.choices.workspace (⟨i.val, hhi⟩ : Fin 640) (by dsimp; omega)
    exact he
  have hc : BankEmpty h.rows.afterCache := by
    intro i hlo hhi
    have hw := alloc.enough.trans alloc.within
    exact (h.rows.cache.work_frame i (by omega) (Or.inr (by omega))
      (by omega) (by omega)).trans (hm i hlo hhi)
  have hl := lagrange_bank_empty h.rows.lagrange hc
  intro i hlo hhi
  exact (h.rows.rows.externalFrame i (by omega)).trans
    ((row_prepared_crt_frame alloc h.rows.afterLagrange i hlo hhi).trans (hl i hlo hhi))

include h in
theorem layout_answer_frame :
    layoutOut.stacks (persistent es 10) = a.stacks (persistent es 10) :=
  (SubexpMainLayoutRows.Result.persistent_frame (List.ofFn h.choices.coefficients)
    h.choices.packing.packing scopes hd h.rows 10 (by decide)).trans
      (h.choices.prefixResult.persistent 10)

end Layout

theorem prepared_crt_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hlo : 320 ≤ i.val) :
    (SubexpMainNodeSetup.prepared alloc a).stacks i = a.stacks i := by
  have h91 : i ≠ ordinary alloc 91 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 91 at hv
    omega
  have h319 : i ≠ ordinary alloc 319 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 319 at hv
    omega
  have ht (j : Fin 4) : SubexpMainNodeHeader.targetPort alloc j ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    fin_cases j <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary] at hv <;> omega
  exact (SubexpMainNodeSetup.prepared_frame alloc a i h91 h319 ht).trans
    (SubexpMainNodePreclear.result_high_frame alloc a i hlo)

section Moments

variable {er es D : ℕ} {alloc : Allocation es} {a initialized : MainState er es}
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc a) initialized D)
  (out : SubexpNodeWideLoop.Data)
  (outReady : SubexpNodeWideLoop.Ready
    (SubexpNodeWorkspace.Ready (SubexpMainMomentData.store alloc initialized)) out)

local notation "final" =>
  SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out

include hi in
theorem final_crt_frame (i : Fin (totalStacks es)) (hlo : 320 ≤ i.val) (hhi : i.val < 640) :
    (final).stacks i = a.stacks i := by
  have h243 : i ≠ ordinary alloc 243 := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 243 at hv
    omega
  exact (SubexpMainMoments.installed_crt_frame alloc _ out i hlo hhi).trans
    ((SubexpMainNodeScratch.result_frame alloc initialized i h243).trans
      ((hi.frame i (SubexpMainMomentPorts.stackMap_avoids_crt alloc i hlo hhi)).trans
        (prepared_crt_frame alloc a i hlo)))

include hi in
theorem final_bank_empty (ha : BankEmpty a) : BankEmpty final := by
  intro i hlo hhi
  exact (final_crt_frame hi out i hlo hhi).trans (ha i hlo hhi)

include hi outReady in
theorem final_persistent_frame (i : Fin 32) :
    (final).stacks (persistent es i) = a.stacks (persistent es i) :=
  SubexpMainMomentCanonicalOutput.persistent_frame hi out outReady i

include outReady in
theorem final_decoder_empty (crtAlloc : SubexpMainCRT.Allocation es) (i : Fin 5) :
    (final).stacks (SubexpMainCRT.decoderScratch crtAlloc i) = [] := by
  have h (j : Fin 256) (h5 : j ≠ 5) (h10 : j ≠ 10)
      (hj : ¬ SubexpNodeWorkspace.MasterPort ⟨j.val, by omega⟩) :
      (final).stacks (ordinary alloc ⟨j.val, by omega⟩) = [] := by
    rw [← SubexpMainMomentPorts.stackMap_native alloc j h5 h10,
      SubexpMainMoments.installed_stack]
    exact SubexpNodeWorkspace.ready_empty outReady.ok ⟨j.val, by omega⟩ hj
  fin_cases i
  · exact h 1 (by decide) (by decide) (by decide)
  · exact h 2 (by decide) (by decide) (by decide)
  · exact h 3 (by decide) (by decide) (by decide)
  · exact h 4 (by decide) (by decide) (by decide)
  · exact h 6 (by decide) (by decide) (by decide)

include hi outReady in
theorem final_ready (crtAlloc : SubexpMainCRT.Allocation es)
    (hbank : BankEmpty a) (hanswer : a.stacks (persistent es 10) = []) :
    SubexpMainCRTBounds.Ready crtAlloc final := by
  constructor
  · intro i
    exact final_bank_empty hi out hbank (SubexpMainCRTBounds.bankPort crtAlloc i)
      (by change 320 ≤ 320 + i.val; omega)
      (by change 320 + i.val < 640; omega)
  · exact final_decoder_empty out outReady crtAlloc
  · exact (final_persistent_frame hi out outReady 10).trans hanswer

include hi outReady in
/-- Only the two actual retained binary word lengths remain after cleanup. -/
theorem inputSize_le {W : ℕ} (hW : RelevantWordBound W a)
    (crtAlloc : SubexpMainCRT.Allocation es) (p Q : ℕ)
    (hbank : BankEmpty a) (hanswer : a.stacks (persistent es 10) = []) :
    SubexpMainCRTBounds.inputSize crtAlloc final p D Q ≤
      p + D + Q + SubexpLiftRing.baseWidth p (D+1) + 2*W + 1 := by
  have hr := final_ready hi out outReady crtAlloc hbank hanswer
  have h19 := SubexpMainLayoutWordBounds.parameter hW 19
    (by unfold SubexpMainInvariant.ParameterPort; decide)
  have h29 := SubexpMainLayoutWordBounds.parameter hW 29
    (by unfold SubexpMainInvariant.ParameterPort; decide)
  rw [SubexpMainCRTBounds.inputSize, hr.auxiliaryBits_eq_zero, Nat.add_zero,
    final_persistent_frame hi out outReady 29, final_persistent_frame hi out outReady 19]
  omega

end Moments

section ActualLayout

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
  {hregs : 16 ≤ er} {alloc : Allocation es}
  {a middle layoutOut initialized : MainState er es} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (out : SubexpNodeWideLoop.Data)
  (outReady : SubexpNodeWideLoop.Ready
    (SubexpNodeWorkspace.Ready (SubexpMainMomentData.store alloc initialized)) out)

local notation "final" =>
  SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out

include h hi outReady in
theorem ready_of_layout (crtAlloc : SubexpMainCRT.Allocation es)
    (hanswer : a.stacks (persistent es 10) = []) :
    SubexpMainCRTBounds.Ready crtAlloc final :=
  final_ready hi out outReady crtAlloc (layout_bank_empty h)
    ((layout_answer_frame h).trans hanswer)

include h hi outReady in
theorem inputSize_le_layout {W : ℕ} (hW : RelevantWordBound W layoutOut)
    (crtAlloc : SubexpMainCRT.Allocation es) (Q : ℕ)
    (hanswer : a.stacks (persistent es 10) = []) :
    SubexpMainCRTBounds.inputSize crtAlloc final p D Q ≤
      p + D + Q + SubexpLiftRing.baseWidth p (D+1) + 2*W + 1 :=
  inputSize_le hi out outReady hW crtAlloc p Q (layout_bank_empty h)
    ((layout_answer_frame h).trans hanswer)

variable {k : ℕ} {tau : ℚ} {F : Type*} [Fintype F]
  {S : Factor.System (Fin D) F (ZMod p)} {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  {layout : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c}

include h hi outReady in
/-- Exact readback arrays and the actual phase frames give the numerical
CRT bound. No global storage bound or CRT runtime certificate is assumed. -/
theorem readback_bound_le_layout {W : ℕ} (hW : RelevantWordBound W layoutOut)
    (crtAlloc : SubexpMainCRT.Allocation es)
    (hanswer : a.stacks (persistent es 10) = [])
    (input : SubexpMainSystemReadback.Readback S layout crtAlloc final) :
    input.bound ≤ 10000000000000000000 *
      (p + D + c.Q + SubexpLiftRing.baseWidth p (D+1) + 2*W + 1)^32 :=
  (SubexpMainSystemCRTBounds.readback_bound_le_dimension input).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (inputSize_le_layout h hi out outReady hW crtAlloc c.Q hanswer) 32))

end ActualLayout

end SubexponentialSAT.SubexpMainMomentCRTBounds

end OAI.Algorithms
