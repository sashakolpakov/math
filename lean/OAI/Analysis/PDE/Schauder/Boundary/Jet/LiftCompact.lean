import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftRaw
import OAI.Analysis.PDE.Nonlinear.CutoffJet
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.BanachData
import OAI.Analysis.Normed.Function.Holder.C2HolderConstruct

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance compactLiftFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance compactLiftFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance compactLiftSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance compactLiftSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def compactBoundaryLift (e : E) (R : ℝ) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E) : ℝ :=
  radialCutoff R x * regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) x

theorem contDiff_compactBoundaryLift (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (R : ℝ) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ContDiff ℝ 2 (compactBoundaryLift e R h) :=
  ((contDiff_radialCutoff R).of_le (by norm_num)).mul
    (contDiff_regularizedBoundaryLift hα hαone e he h)

theorem hasCompactSupport_compactBoundaryLift (e : E) {R : ℝ} (hR : 0 < R)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) : HasCompactSupport (compactBoundaryLift e R h) :=
  (hasCompactSupport_radialCutoff hR).mul_right

theorem exists_compactBoundaryLift_hessian_holder (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) {R : ℝ} (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] E →L[ℝ] ℝ) α,
      ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ (compactBoundaryLift e R h)) x := by
  obtain ⟨C, hC, hh⟩ := exists_regularizedBoundaryLift_hessian_holder hα hαone e he h
  exact OAI.Analysis.PDE.Nonlinear.exists_cutoff_hessian_holder (radialCutoff R)
    (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))
    ((contDiff_radialCutoff R).of_le (by norm_num)) (hasCompactSupport_radialCutoff hR)
    (contDiff_regularizedBoundaryLift hα hαone e he h) 0
    (r := 2 * R) (R := 2 * R + 1) (by linarith) (by linarith) hα.le hαone.le hC
    (fun x ↦ ⟨radialCutoff_nonneg R x, radialCutoff_le_one R x⟩)
    (by
      intro x hx
      apply radialCutoff_zero hR
      have := not_le.mp (show ¬ ‖x‖ ≤ 2 * R by simpa only [mem_closedBall, dist_zero_right] using hx)
      linarith)
    (fun x _ y _ ↦ hh x y)

theorem exists_globalC2Holder_compactBoundaryLift (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) {R : ℝ} (hR : 0 < R) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ∃ W : GlobalC2Holder m α,
      ∀ x : E, OAI.Analysis.Normed.Function.Holder.C2Holder.value W ⟨x, mem_univ x⟩ = compactBoundaryLift e R h x := by
  let f := compactBoundaryLift e R h
  have hf : ContDiff ℝ 2 f := contDiff_compactBoundaryLift hα hαone e he R h
  have hfc : HasCompactSupport f := hasCompactSupport_compactBoundaryLift e hR h
  obtain ⟨H, hH⟩ := exists_compactBoundaryLift_hessian_holder hα hαone e he hR h
  obtain ⟨M0, h0⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨M1, h1⟩ := (hfc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hf.fderiv_right (m := 1) (by norm_num)).continuous
  have h2 (x : E) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ ‖H‖ := by
    rw [← hH x]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le H x
  have hh (x y : E) : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖H‖ * dist x y ^ α := by
    rw [← hH x, ← hH y]
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le H x y
  exact ⟨OAI.Analysis.Normed.Function.Holder.C2Holder.ofContDiff isOpen_univ (Subset.rfl : (univ : Set E) ⊆ univ) hα.le f hf
    (fun x _ ↦ h0 x) (fun x _ ↦ h1 x) (fun x _ ↦ h2 x) (fun x _ y _ ↦ hh x y),
    fun _ ↦ rfl⟩

end OAI.Analysis.PDE.Schauder
