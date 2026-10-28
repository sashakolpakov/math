import OAI.Analysis.PDE.Dirichlet.LogData
import Mathlib.Analysis.Calculus.MeanValue

open Set
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem exists_log_lipschitz_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hpos : ∀ x ∈ K, 0 < F x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      |Real.log (F x) - Real.log (F y)| ≤ L * dist x y := by
  have hloc (x : E) (hx : x ∈ K) : ContDiffAt ℝ 2 (fun z ↦ Real.log (F z)) x :=
    hF.contDiffAt.log (hpos x hx).ne'
  have hc : ContinuousOn (fun x ↦ ‖fderiv ℝ (fun z ↦ Real.log (F z)) x‖) K := by
    intro x hx
    exact ((hloc x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hK.bddAbove_image hc
  let L := max D 0 + 1
  have hbound (x : E) (hx : x ∈ K) : ‖fderiv ℝ (fun z ↦ Real.log (F z)) x‖ ≤ L :=
    (hD (mem_image_of_mem _ hx)).trans (by dsimp [L]; linarith [le_max_left D 0])
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x hx ↦ (hloc x hx).differentiableAt (by norm_num)) hbound hconv hy hx
  simpa only [Real.norm_eq_abs, dist_eq_norm] using h

end OAI.Analysis.PDE.Dirichlet
