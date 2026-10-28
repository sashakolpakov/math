import OAI.Analysis.PDE.Schauder.Calculus.Schauder.EllipticLocal
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

/-! The elliptic Hölder bootstrap needs C² regularity only on the open PDE domain. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem elliptic_interior_schauder {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩ : IsOpen Ω)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiffOn ℝ 2 u Ω)
    (hPD : ∀ x ∈ Ω, (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef)
    (heq : ∀ x ∈ Ω, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x)
    (x₀ : EuclideanSpace ℝ (Fin m)) (hx₀ : x₀ ∈ Ω) :
    ∃ s > 0, ∃ C > 0, ∀ x ∈ ball x₀ s, ∀ y ∈ ball x₀ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨g, hg, hgu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point
    ((hu x₀ hx₀).contDiffAt (hΩ.mem_nhds hx₀))
  have hD : fderiv ℝ (fderiv ℝ g) =ᶠ[𝓝 x₀] fderiv ℝ (fderiv ℝ u) :=
    (hgu.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hΩev : ∀ᶠ x in 𝓝 x₀, x ∈ Ω := hΩ.mem_nhds hx₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hΩev.and hD)
  have hPDg (x) (hx : x ∈ ball x₀ r) : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef := hPD x (hball hx).1
  have heqg (x) (hx : x ∈ ball x₀ r) :
      nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) g x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x := by
    unfold nondivergenceOperator
    rw [(hball hx).2]
    exact heq x (hball hx).1
  obtain ⟨s, hs, C, hC, hh⟩ := elliptic_pointwise_schauder hm hα hα1 hr A F g hg x₀ hPDg heqg
  refine ⟨min r s, lt_min hr hs, C, hC, ?_⟩
  intro x hx y hy
  have hxr : x ∈ ball x₀ r := ball_subset_ball (min_le_left r s) hx
  have hyr : y ∈ ball x₀ r := ball_subset_ball (min_le_left r s) hy
  have hxs : x ∈ ball x₀ s := ball_subset_ball (min_le_right r s) hx
  have hys : y ∈ ball x₀ s := ball_subset_ball (min_le_right r s) hy
  have h := hh x hxs y hys
  rwa [(hball hxr).2, (hball hyr).2] at h

end OAI.Analysis.PDE.Schauder
