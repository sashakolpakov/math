import OAI.Analysis.PDE.Dirichlet.Boundary.Fields
import OAI.Analysis.PDE.Dirichlet.Uniform.Taylor

open Set Metric
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

theorem continuous_boundaryFieldFactor {P : Type*} [TopologicalSpace P] {n : ℕ}
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r)
    {z e : P → CoordinateSpace n 4} (hz : Continuous z) (he : Continuous e)
    (hreg : ∀ p, fderiv ℝ r (z p) ≠ 0) :
    Continuous (fun p ↦ boundaryFieldFactor r (z p) (e p)) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ r) := hr.fderiv_right (by norm_num)
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ r)) :=
    (hD.fderiv_right (m := 0) (by norm_num)).continuous
  have hν : Continuous (fun p ↦ covectorNormal (fderiv ℝ r (z p))) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact continuousAt_covectorNormal (hD.continuous.comp hz).continuousAt (hreg p)
  exact (((hD2.comp hz).clm_apply hν).clm_apply he).div (hD.continuous.comp hz).norm
    (fun p ↦ norm_ne_zero_iff.mpr (hreg p))

/-- Quadratic boundary vanishing is uniform over a compact family of centers
and tangent directions, on the fixed radius-one neighborhood. -/
theorem exists_compact_boundary_quadratic
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {n : ℕ}
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r)
    {z e : P → CoordinateSpace n 4} (hz : Continuous z) (he : Continuous e)
    (hreg : ∀ p, fderiv ℝ r (z p) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p, r (z p) = 0 → fderiv ℝ r (z p) (e p) = 0 →
      ∀ y, ‖y - z p‖ ≤ 1 → r y = 0 →
        |affineDerivative r (boundaryFieldTranslation r (z p) (e p))
          (boundaryFieldLinear r (z p) (e p)) y| ≤ C * ‖y - z p‖ ^ 2 := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hRot := continuous_boundaryRotation hr2 hz he hreg
  have hA : Continuous (fun p ↦ boundaryFieldLinear r (z p) (e p)) :=
    continuous_realMatrixAction.comp (continuous_realRepresentation hRot)
  have htrans : Continuous (fun p ↦ boundaryFieldTranslation r (z p) (e p)) :=
    he.sub (hA.clm_apply hz)
  obtain ⟨R₀, hR₀⟩ := (isCompact_univ : IsCompact (univ : Set P)).bddAbove_image hz.norm.continuousOn
  let R := max R₀ 0 + 2
  let W := closedBall (0 : CoordinateSpace n 4) R
  have hW : IsCompact W := isCompact_closedBall _ _
  have hball : ∀ p, closedBall (z p) 1 ⊆ W := by
    intro p y hy
    have hzR : ‖z p‖ ≤ R₀ := hR₀ (mem_image_of_mem _ (mem_univ p))
    have hyz : ‖y - z p‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hy
    have hn : ‖y‖ ≤ ‖y - z p‖ + ‖z p‖ := by simpa only [sub_add_cancel] using norm_add_le (y - z p) (z p)
    change dist y 0 ≤ R
    rw [dist_zero_right]
    dsimp [R]
    linarith [le_max_left R₀ 0]
  obtain ⟨D, hD, hDf⟩ := exists_compact_family_affine_hessian_bound hr htrans hA hW
  have hD2 : Continuous (fun x ↦ ‖fderiv ℝ (fderiv ℝ r) x‖) :=
    (((hr2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous).norm
  obtain ⟨B₀, hB₀⟩ := hW.bddAbove_image hD2.continuousOn
  let B := max B₀ 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hDr : ∀ y ∈ W, ‖fderiv ℝ (fderiv ℝ r) y‖ ≤ B := by
    intro y hy
    have h := hB₀ (mem_image_of_mem _ hy)
    exact h.trans (by dsimp [B]; linarith [le_max_left B₀ 0])
  have hfac := continuous_boundaryFieldFactor hr2 hz he hreg
  obtain ⟨L₀, hL₀⟩ := (isCompact_univ : IsCompact (univ : Set P)).bddAbove_image hfac.abs.continuousOn
  let L := max L₀ 0 + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hfactor : ∀ p, |boundaryFieldFactor r (z p) (e p)| ≤ L := by
    intro p
    have h := hL₀ (mem_image_of_mem _ (mem_univ p))
    exact h.trans (by dsimp [L]; linarith [le_max_left L₀ 0])
  refine ⟨D + L * B, by positivity, ?_⟩
  intro p hrp hep y hy hry
  have hfx : affineDerivative r (boundaryFieldTranslation r (z p) (e p))
      (boundaryFieldLinear r (z p) (e p)) (z p) = 0 := by
    simpa only [affineDerivative, boundaryFieldTranslation, sub_add_cancel] using hep
  apply quadratic_level_set_bound_from_data
    (contDiff_affineDerivative hr (by norm_num) _ _) hr2 hfx hrp
    (boundaryField_first_jet hr2 (hreg p) (e p)) hL.le hD.le hB.le (by norm_num)
    (hfactor p) (fun t ht ↦ hDf p t (hball p ht)) (fun t ht ↦ hDr t (hball p ht)) y
    (by simpa only [mem_closedBall, dist_eq_norm] using hy) hry

end OAI.Analysis.PDE.Dirichlet
