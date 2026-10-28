import OAI.Analysis.PDE.Dirichlet.InteriorHolderOnSet
import OAI.Analysis.PDE.Dirichlet.LogData
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- Interior Hölder bounds on an arbitrary compact subset. The logarithmic
data bounds and a common ball radius are derived from compactness, not assumed. -/
theorem log_equation_holder_on_compact {n : ℕ} {lam L V : ℝ}
    (hlam : 0 < lam) (hL : lam ≤ L) (hV : 0 ≤ V)
    {Ω K : Set (CoordinateSpace (n + 1) 4)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (F : CoordinateSpace (n + 1) 4 → ℝ) (hF : ContDiff ℝ 2 F)
    (hFpos : ∀ x ∈ Ω, 0 < F x) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ ψ : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 ψ →
      (∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) →
      (∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x) →
      (∀ x ∈ Ω, ∀ v,
        lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) v ≤ L * ‖v‖ ^ 2) →
      (∀ x ∈ Ω, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ V) →
      ∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B * (dist x y) ^ α := by
  obtain ⟨R, hR, hthick⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let U := cthickening R K
  have hU : IsCompact U := hK.cthickening
  have hUΩ : U ⊆ Ω := hthick
  have hloc (x) (hx : x ∈ U) : ContDiffAt ℝ 2 (fun y ↦ Real.log (F y)) x :=
    hF.contDiffAt.log (hFpos x (hUΩ hx)).ne'
  have hc : ContinuousOn (fun x ↦ ‖fderiv ℝ (fun y ↦ Real.log (F y)) x‖) U := by
    intro x hx
    exact ((hloc x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hU.bddAbove_image hc
  let L₁ := max D 0 + 1
  have hL₁ : 0 < L₁ := by dsimp [L₁]; positivity
  have hlog (x) (hx : x ∈ U) : ‖fderiv ℝ (fun y ↦ Real.log (F y)) x‖ ≤ L₁ :=
    (hD (mem_image_of_mem _ hx)).trans (by dsimp [L₁]; linarith [le_max_left D 0])
  obtain ⟨L₂, hL₂, hlog₂⟩ := exists_log_second_directional_bound hF hU
    (fun x hx ↦ hFpos x (hUΩ hx))
  obtain ⟨α, B, hα, hα1, hB, hbound⟩ := log_equation_holder_on_interior_set
    (n := n) hlam hL hL₁.le hL₂.le hV hR
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro ψ hψ hpos heq hell hnorm
  apply hbound U K ψ F ?_ hψ
    (fun x hx ↦ hpos x (hUΩ hx))
    (fun x hx ↦ heq x (hUΩ hx))
    (fun x hx v ↦ hell x (hUΩ hx) v)
    (fun x hx ↦ hnorm x (hUΩ hx))
    (fun x hx ↦ (hloc x hx).differentiableAt (by norm_num)) hlog hlog₂
  intro z hz
  exact (closedBall_subset_cthickening_singleton z R).trans
    (cthickening_subset_of_subset R (singleton_subset_iff.mpr hz))

end OAI.Analysis.PDE.Dirichlet
