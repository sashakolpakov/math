import Mathlib

/-! Smoothness can be checked after the isometric inclusion of a complete linear
subspace.  Closedness enters through limits of difference quotients, not through
any assumed differentiability of a choice of inverse. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section

namespace OAI.Analysis.Normed.Operator.ClosedSubspace

universe u

variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def postcompIsometry (e : F →ₗᵢ[ℝ] G) :
    (E →L[ℝ] F) →ₗᵢ[ℝ] (E →L[ℝ] G) where
  toLinearMap := (ContinuousLinearMap.compL ℝ E F G e.toContinuousLinearMap).toLinearMap
  norm_map' L := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
      intro x
      simpa using L.le_opNorm x
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      simpa using (e.toContinuousLinearMap.comp L).le_opNorm x

@[simp] theorem postcompIsometry_apply (e : F →ₗᵢ[ℝ] G) (L : E →L[ℝ] F) :
    postcompIsometry e L = e.toContinuousLinearMap.comp L := rfl

theorem hasFDerivAt_of_isometry (e : F →ₗᵢ[ℝ] G) {f : E → F}
    {L : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt (fun y ↦ e (f y)) (e.toContinuousLinearMap.comp L) x) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_tendsto] at h ⊢
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    ← map_sub, LinearIsometry.norm_map] using h

theorem exists_hasFDerivAt_of_isometry [CompleteSpace F]
    (e : F →ₗᵢ[ℝ] G) {f : E → F} {D : E →L[ℝ] G} {x : E}
    (h : HasFDerivAt (fun y ↦ e (f y)) D x) :
    ∃ L : E →L[ℝ] F, HasFDerivAt f L x ∧ e.toContinuousLinearMap.comp L = D := by
  have hclosed : IsClosed (Set.range e) := e.isometry.isClosedEmbedding.isClosed_range
  have hmem (v : E) : D v ∈ e.toLinearMap.range := by
    apply hclosed.mem_of_tendsto (h.lim v tendsto_norm_atTop_atTop)
    exact Filter.Eventually.of_forall fun t : ℝ ↦
      ⟨t • (f (x + t⁻¹ • v) - f x), by simp⟩
  let L : E →L[ℝ] F := e.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (D.codRestrict e.toLinearMap.range hmem)
  have heq : e.toContinuousLinearMap.comp L = D := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := e.equivRange.apply_symm_apply ⟨D v, hmem v⟩
    exact congrArg Subtype.val hv
  exact ⟨L, hasFDerivAt_of_isometry e (heq.symm ▸ h), heq⟩

theorem contDiff_nat_of_isometry [CompleteSpace F]
    (e : F →ₗᵢ[ℝ] G) {f : E → F} (n : ℕ)
    (h : ContDiff ℝ n (fun x ↦ e (f x))) : ContDiff ℝ n f := by
  induction n generalizing F G with
  | zero =>
    exact contDiff_zero.mpr (e.isometry.isEmbedding.continuous_iff.mpr h.continuous)
  | succ n ih =>
    obtain ⟨D, hD, hd⟩ := contDiff_succ_iff_hasFDerivAt.mp h
    choose L hL heq using fun x ↦ exists_hasFDerivAt_of_isometry e (hd x)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨L, ?_, hL⟩
    apply ih (postcompIsometry e)
    simpa only [postcompIsometry_apply, heq] using hD

theorem contDiff_infty_of_isometry [CompleteSpace F]
    (e : F →ₗᵢ[ℝ] G) {f : E → F}
    (h : ContDiff ℝ ∞ (fun x ↦ e (f x))) : ContDiff ℝ ∞ f := by
  rw [contDiff_infty] at h ⊢
  exact fun n ↦ contDiff_nat_of_isometry e n (h n)

end OAI.Analysis.Normed.Operator.ClosedSubspace
