import OAI.Analysis.PDE.Nonlinear.SmoothHolder
import OAI.Analysis.PDE.Dirichlet.MatrixTransport
import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry

/-! Local Schauder regularity in an arbitrary finite Euclidean coordinate system. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

theorem indexed_C1_coefficient_schauder {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (e : I ≃ Fin m) (hm : 3 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (u f : EuclideanSpace ℝ I → ℝ)
    (x₀ : EuclideanSpace ℝ I) (hA : ContDiffAt ℝ 1 A x₀) (hu : ContDiff ℝ 2 u)
    (hf : ContDiffAt ℝ 1 f x₀)
    (hPD : ∀ᶠ x in 𝓝 x₀, (A x).PosDef)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator A u x = f x) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  let L := OAI.Analysis.PDE.Dirichlet.coordinateReindex e.symm
  let P := OAI.Analysis.PDE.Dirichlet.coordinateReindex e
  let y₀ := P x₀
  have hLx : L y₀ = x₀ := OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x₀
  let B := fun y => OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm (A (L y))
  let v := u ∘ L
  let g := f ∘ L
  have hB : ContDiffAt ℝ 1 B y₀ := by
    apply (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm).contDiff.contDiffAt.comp
    exact (hLx ▸ hA).comp y₀ L.contDiff.contDiffAt
  have hv : ContDiff ℝ 2 v := hu.comp L.contDiff
  have hg : ContDiffAt ℝ 1 g y₀ := (hLx ▸ hf).comp y₀ L.contDiff.contDiffAt
  have ht : Tendsto L (𝓝 y₀) (𝓝 x₀) := by simpa only [hLx] using L.continuous.tendsto y₀
  have hBP : ∀ᶠ y in 𝓝 y₀, (B y).PosDef := by
    filter_upwards [ht.eventually hPD] with y hy
    exact OAI.Analysis.PDE.Dirichlet.matrixReindex_posDef e.symm hy
  have hBeq : ∀ᶠ y in 𝓝 y₀, OAI.Analysis.PDE.Schauder.nondivergenceOperator B v y = g y := by
    filter_upwards [ht.eventually hPDE] with y hy
    exact (OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator_reindex e.symm A u hu y).trans hy
  obtain ⟨r, hr, C, hC, hh⟩ := local_C1_coefficient_schauder hm hα hα1 B v g y₀ hB hv.contDiffAt hg hBP hBeq
  have hvP : v ∘ P = u := by
    funext x
    exact congrArg u (OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x)
  refine ⟨r, hr, C, hC, ?_⟩
  intro x hx y hy
  have hx' : P x ∈ ball y₀ r := by simpa only [mem_ball, y₀, P.dist_map] using hx
  have hy' : P y ∈ ball y₀ r := by simpa only [mem_ball, y₀, P.dist_map] using hy
  have hb := OAI.Analysis.Normed.Function.Holder.bilinear_norm_le_isometric_pullback P
    (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
    (fderiv ℝ (fderiv ℝ v) (P x) - fderiv ℝ (fderiv ℝ v) (P y)) (by
      intro a b
      simp only [sub_apply]
      apply congrArg₂ (· - ·)
      · have ht := OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between v hv P.toContinuousLinearEquiv.toContinuousLinearMap x a b
        change fderiv ℝ (fderiv ℝ (v ∘ P)) x a b = _ at ht
        rwa [hvP] at ht
      · have ht := OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between v hv P.toContinuousLinearEquiv.toContinuousLinearMap y a b
        change fderiv ℝ (fderiv ℝ (v ∘ P)) y a b = _ at ht
        rwa [hvP] at ht)
  apply hb.trans
  simpa only [← dist_eq_norm, P.dist_map] using hh (P x) hx' (P y) hy'

end OAI.Analysis.PDE.Nonlinear
