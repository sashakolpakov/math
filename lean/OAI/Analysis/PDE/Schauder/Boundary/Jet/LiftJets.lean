import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftCompact
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Laplacian

noncomputable section
open Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance jetsFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance jetsFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance jetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance jetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem compactBoundaryLift_zero (e : E) (R : ℝ) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α)
    (x : E) (hx : inner ℝ e x = 0) : compactBoundaryLift e R h x = 0 := by
  simp only [compactBoundaryLift, regularizedBoundaryLift_zero e _ hx, mul_zero]

theorem fderiv_compactBoundaryLift_zero (e : E) (he : ‖e‖ = 1) (R : ℝ)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E) (hx : inner ℝ e x = 0) :
    fderiv ℝ (compactBoundaryLift e R h) x = 0 := by
  have hf := hasFDerivAt_regularizedBoundaryLift_boundary e he h hx
  have hp := ((contDiff_radialCutoff R).differentiable (by simp) x).hasFDerivAt.mul hf
  change fderiv ℝ (radialCutoff R * regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h)) x = 0
  simpa only [regularizedBoundaryLift_zero e _ hx, zero_smul, smul_zero, add_zero] using hp.fderiv

theorem hessian_compactBoundaryLift_boundary (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (R : ℝ) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α)
    (x : E) (hx : inner ℝ e x = 0) :
    fderiv ℝ (fderiv ℝ (compactBoundaryLift e R h)) x =
      (radialCutoff R x * OAI.Analysis.Normed.Function.Holder.HolderMap.value h x) • (innerSL ℝ e).smulRight (innerSL ℝ e) := by
  have hf := (hasFDerivAt_regularizedBoundaryLift_boundary e he h hx).fderiv
  have hh := OAI.Analysis.PDE.Nonlinear.cutoff_hessian (radialCutoff R)
    (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))
    ((contDiff_radialCutoff R).of_le (by norm_num))
    (contDiff_regularizedBoundaryLift hα hαone e he h) x
  change fderiv ℝ (fderiv ℝ (fun y ↦ radialCutoff R y *
    regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) y)) x = _
  rw [hh, fderiv_fderiv_regularizedBoundaryLift_boundary hα e he h x hx]
  ext v w
  simp [OAI.Analysis.PDE.Nonlinear.cutoffCommutator, regularizedBoundaryLift_zero e _ hx, hf,
    smul_eq_mul, mul_assoc]

theorem hessian_compactBoundaryLift_supported_boundary (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) {R : ℝ} (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α)
    (hs : ∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value h x = 0)
    (x : E) (hx : inner ℝ e x = 0) :
    fderiv ℝ (fderiv ℝ (compactBoundaryLift e R h)) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value h x • (innerSL ℝ e).smulRight (innerSL ℝ e) := by
  rw [hessian_compactBoundaryLift_boundary hα hαone e he R h x hx]
  by_cases hxr : ‖x‖ ≤ R
  · rw [radialCutoff_one hR hxr, one_mul]
  · rw [hs x (lt_of_not_ge hxr), mul_zero]

theorem laplacian_compactBoundaryLift_boundary (hα : 0 < α) (hαone : α < 1)
    (k : Fin m) {R : ℝ} (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α)
    (hs : ∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value h x = 0)
    (x : E) (hx : x k = 0) :
    laplacian (compactBoundaryLift (EuclideanSpace.single k 1) R h) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value h x := by
  have hinner : inner ℝ (EuclideanSpace.single k 1) x = 0 := by
    simpa [EuclideanSpace.inner_single_left] using hx
  rw [laplacian_eq_normal_boundary k _
    (contDiff_compactBoundaryLift hα hαone _ (by simp) R h)
    (fun y hy ↦ compactBoundaryLift_zero _ R h y (by simpa [EuclideanSpace.inner_single_left] using hy)) x hx]
  rw [hessian_compactBoundaryLift_supported_boundary hα hαone _ (by simp) hR h hs x hinner]
  simp [ContinuousLinearMap.smulRight_apply]

end OAI.Analysis.PDE.Schauder
