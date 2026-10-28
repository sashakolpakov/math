import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftBounded
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftJets

noncomputable section
open Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance liftFinalFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance liftFinalFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance liftFinalSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance liftFinalSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A genuine compactly supported C²,α normal-jet lift of Hölder boundary data.
Its value and full gradient vanish at the boundary, and its normal-normal
second derivative (equivalently, its Laplacian there) is the prescribed datum. -/
theorem exists_boundary_jet_lift (k : Fin m) (hα : 0 < α) (hαone : α < 1) (hR : 0 < R) :
    ∃ C > 0, ∀ h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
      (∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value h x = 0) →
      ∃ W : GlobalC2Holder m α,
        ‖W‖ ≤ C * ‖h‖ ∧ HasCompactSupport (OAI.Analysis.Normed.Function.Holder.fullValue W) ∧
        (∀ x, 2 * R ≤ ‖x‖ → OAI.Analysis.Normed.Function.Holder.fullValue W x = 0) ∧
        (∀ x, x k = 0 → OAI.Analysis.Normed.Function.Holder.fullValue W x = 0) ∧
        (∀ x, x k = 0 → fderiv ℝ (OAI.Analysis.Normed.Function.Holder.fullValue W) x = 0) ∧
        (∀ x, x k = 0 → fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.fullValue W)) x
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) = OAI.Analysis.Normed.Function.Holder.HolderMap.value h x) ∧
        (∀ x, x k = 0 → laplacian (OAI.Analysis.Normed.Function.Holder.fullValue W) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value h x) := by
  let e : E := EuclideanSpace.single k 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := boundaryLiftCLM hα hαone e he hR
  refine ⟨‖T‖ + 1, by positivity, ?_⟩
  intro h hs
  have hvalue : OAI.Analysis.Normed.Function.Holder.fullValue (T h) = compactBoundaryLift e R h := by
    funext x
    exact boundaryLiftCLM_value hα hαone e he hR h x
  refine ⟨T h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (T.le_opNorm h).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg h))
  · rw [hvalue]
    exact hasCompactSupport_compactBoundaryLift e hR h
  · intro x hx
    rw [hvalue]
    simp only [compactBoundaryLift, radialCutoff_zero hR hx, zero_mul]
  · intro x hx
    rw [hvalue]
    exact compactBoundaryLift_zero e R h x (by simpa [e, EuclideanSpace.inner_single_left] using hx)
  · intro x hx
    rw [hvalue]
    exact fderiv_compactBoundaryLift_zero e he R h x
      (by simpa [e, EuclideanSpace.inner_single_left] using hx)
  · intro x hx
    rw [hvalue, hessian_compactBoundaryLift_supported_boundary hα hαone e he hR h hs x
      (by simpa [e, EuclideanSpace.inner_single_left] using hx)]
    simp [e, ContinuousLinearMap.smulRight_apply]
  · intro x hx
    rw [hvalue]
    exact laplacian_compactBoundaryLift_boundary hα hαone k hR h hs x hx

theorem exists_boundary_jet_lift_function (k : Fin m) (hα : 0 < α) (hαone : α < 1) (hR : 0 < R) :
    ∃ C > 0, ∀ h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
      (∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value h x = 0) →
      ∃ W : E → ℝ,
        ContDiff ℝ 2 W ∧ HasCompactSupport W ∧
        (∀ x, x k = 0 → W x = 0) ∧
        (∀ x, x k = 0 → fderiv ℝ W x = 0) ∧
        (∀ x, x k = 0 → laplacian W x = OAI.Analysis.Normed.Function.Holder.HolderMap.value h x) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y‖ ≤
          (C * ‖h‖) * ‖x - y‖ ^ α) := by
  obtain ⟨C, hC, hlift⟩ := exists_boundary_jet_lift k hα hαone hR
  refine ⟨C, hC, ?_⟩
  intro h hs
  obtain ⟨W, hnorm, hc, _, hzero, hfirst, _, hlap⟩ := hlift h hs
  refine ⟨OAI.Analysis.Normed.Function.Holder.fullValue W, OAI.Analysis.Normed.Function.Holder.contDiff_fullValue W, hc, hzero, hfirst, hlap, ?_⟩
  intro x y
  exact (OAI.Analysis.Normed.Function.Holder.fullValue_second_holder W x y).trans (by
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg (norm_nonneg _) _))

/-- The lifting constant can be chosen uniformly among all coordinate normals. -/
theorem exists_boundary_jet_lift_uniform (m : ℕ) {α R : ℝ}
    (hα : 0 < α) (hαone : α < 1) (hR : 0 < R) :
    ∃ C > 0, ∀ (k : Fin m) (h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α),
      (∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value h x = 0) →
      ∃ W : EuclideanSpace ℝ (Fin m) → ℝ,
        ContDiff ℝ 2 W ∧ HasCompactSupport W ∧
        (∀ x, x k = 0 → W x = 0) ∧
        (∀ x, x k = 0 → fderiv ℝ W x = 0) ∧
        (∀ x, x k = 0 → laplacian W x = OAI.Analysis.Normed.Function.Holder.HolderMap.value h x) ∧
        (∀ x y, ‖fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y‖ ≤
          (C * ‖h‖) * ‖x - y‖ ^ α) := by
  choose c hc hlift using (fun k : Fin m ↦ exists_boundary_jet_lift_function k hα hαone hR)
  have hsum : 0 ≤ ∑ k, c k := Finset.sum_nonneg (fun k _ ↦ (hc k).le)
  refine ⟨(∑ k, c k) + 1, by linarith, ?_⟩
  intro k h hs
  obtain ⟨W, hw, hwc, hz, hf, hl, hholder⟩ := hlift k h hs
  refine ⟨W, hw, hwc, hz, hf, hl, ?_⟩
  have hck : c k ≤ (∑ j, c j) + 1 := by
    have hle := Finset.single_le_sum (f := c) (fun j _ ↦ (hc j).le) (Finset.mem_univ k)
    linarith
  intro x y
  exact (hholder x y).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hck (norm_nonneg h)) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
