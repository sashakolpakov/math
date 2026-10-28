import OAI.Analysis.HodgeTheory.Decomposition.FreezingError
import OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy

/-! # Supported Operator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SupportedOperator.Constructions

noncomputable section

/-! A first-order operator with locally smooth coefficients preserves smooth
compact support when the input is supported inside the coefficient domain. -/

open scoped _root_.Topology ContDiff BigOperators SchwartzMap

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]

def localFirstOrderValue (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) (x : E) : G :=
  (∑ i, C i x (fderiv ℝ u x (directions i))) + Z x (u x)

theorem localFirstOrderValue_tsupport (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) :
    tsupport (localFirstOrderValue C Z directions u) ⊆ tsupport u := by
  apply closure_minimal ?_ (isClosed_tsupport u)
  intro x hx
  by_contra hxu
  apply hx
  simp [localFirstOrderValue, fderiv_of_notMem_tsupport ℝ hxu,
    image_eq_zero_of_notMem_tsupport hxu]

theorem localFirstOrderValue_smooth
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) (hu : ContDiff ℝ ∞ u)
    {U : Set E} (hU : IsOpen U) (hs : tsupport u ⊆ U)
    (hC : ∀ i, ContDiffOn ℝ ∞ (C i) U) (hZ : ContDiffOn ℝ ∞ Z U) :
    ContDiff ℝ ∞ (localFirstOrderValue C Z directions u) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport u
  · have hxU := hU.mem_nhds (hs hx)
    have hD (i : ι) : ContDiffAt ℝ ∞ (fun y => fderiv ℝ u y (directions i)) x :=
      ((hu.contDiffAt.fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact (ContDiffAt.sum (fun i _ => ((hC i).contDiffAt hxU).clm_apply (hD i))).add
      ((hZ.contDiffAt hxU).clm_apply hu.contDiffAt)
  · have hout : x ∉ tsupport (localFirstOrderValue C Z directions u) :=
      fun h => hx (localFirstOrderValue_tsupport C Z directions u h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hout)

theorem localFirstOrderValue_compactSupport
    (C : ι → E → F →L[ℝ] G) (Z : E → F →L[ℝ] G)
    (directions : ι → E) (u : E → F) (hu : HasCompactSupport u) :
    HasCompactSupport (localFirstOrderValue C Z directions u) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (localFirstOrderValue_tsupport C Z directions u)

end

end OAI.Analysis.HodgeTheory.Decomposition.SupportedOperator.Constructions
