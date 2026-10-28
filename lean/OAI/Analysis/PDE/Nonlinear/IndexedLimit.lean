import OAI.Analysis.PDE.Nonlinear.EllipticLimit
import OAI.Analysis.PDE.Dirichlet.MatrixTransport

/-! The regularity limit theorem in any finite Euclidean coordinate system. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

theorem indexed_family_limit_C2 {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (e : I ≃ Fin m) (hm : 3 ≤ m) {α ρ δ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (Matrix I I ℝ) α)
    (hA : ∀ h, ‖A h‖ ≤ M) (x₀ : EuclideanSpace ℝ I)
    (A₀ : Matrix I I ℝ) (hA₀ : A₀.PosDef)
    (hAlim : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) (𝓝 0) (𝓝 A₀))
    (u : ℝ → EuclideanSpace ℝ I → ℝ)
    (hu : ∀ h, h ≠ 0 → |h| < δ → ContDiff ℝ 2 (u h))
    (U : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α)
    (V : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) (EuclideanSpace ℝ I →L[ℝ] ℝ) α)
    (F : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ I) ℝ α)
    (hU : ∀ h, h ≠ 0 → |h| < δ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (U h) x = u h x)
    (hV : ∀ h, h ≠ 0 → |h| < δ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (V h) x = fderiv ℝ (u h) x)
    {N₀ N₁ Nf : ℝ} (hUN : ∀ h, h ≠ 0 → |h| < δ → ‖U h‖ ≤ N₀)
    (hVN : ∀ h, h ≠ 0 → |h| < δ → ‖V h‖ ≤ N₁)
    (hFN : ∀ h, h ≠ 0 → |h| < δ → ‖F h‖ ≤ Nf)
    (hPD : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x).PosDef)
    (heq : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ,
      OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (u h) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F h) x)
    (w : EuclideanSpace ℝ I → ℝ)
    (hw : ∀ x, Tendsto (fun h => u h x) (𝓝[≠] 0) (𝓝 (w x))) :
    ContDiffAt ℝ 2 w x₀ := by
  let L := OAI.Analysis.PDE.Dirichlet.coordinateReindex e.symm
  let y₀ := OAI.Analysis.PDE.Dirichlet.coordinateReindex e x₀
  have hLx : L y₀ = x₀ := OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x₀
  let J : (EuclideanSpace ℝ I →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ _ _ _).flip L.toContinuousLinearEquiv.toContinuousLinearMap
  let A' := fun h => OAI.Analysis.PDE.Dirichlet.coefficientReindex hα.le e.symm (A h)
  let U' := fun h => OAI.Analysis.PDE.Schauder.holderIsometricPullback hα.le L L.isometry (U h)
  let V' := fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM J (OAI.Analysis.PDE.Schauder.holderIsometricPullback hα.le L L.isometry (V h))
  let F' := fun h => OAI.Analysis.PDE.Schauder.holderIsometricPullback hα.le L L.isometry (F h)
  let u' := fun h => u h ∘ L
  have hnear (y) (hy : y ∈ ball y₀ ρ) : L y ∈ ball x₀ ρ := by
    rw [← hLx]
    simpa only [mem_ball, L.dist_map] using hy
  have hA' (h) : ‖A' h‖ ≤ M := (OAI.Analysis.PDE.Dirichlet.norm_coefficientReindex_le hα.le e.symm (A h)).trans (hA h)
  have hAlim' : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) y₀) (𝓝 0)
      (𝓝 (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm A₀)) := by
    have ht := (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm).continuous.continuousAt.tendsto.comp hAlim
    have he (h) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) y₀ = OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) := by
      apply Matrix.ext
      intro i j
      change OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) (L y₀) (e.symm i) (e.symm j) = _
      rw [hLx]
      rfl
    simpa only [he, Function.comp_def] using ht
  have hU' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (U' h) y = u' h y := hU h hh hd (L y)
  have hV' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (V' h) y = fderiv ℝ (u' h) y := by
    change (OAI.Analysis.Normed.Function.Holder.HolderMap.value (V h) (L y)).comp L.toContinuousLinearEquiv.toContinuousLinearMap = _
    rw [hV h hh hd]
    have ht := (((hu h hh hd).differentiable (by norm_num) (L y)).hasFDerivAt.comp y
      L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
    simpa only [u', Function.comp_def] using! ht.symm
  have hUN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖U' h‖ ≤ N₀ :=
    (OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα.le L L.isometry _).trans (hUN h hh hd)
  have hVN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖V' h‖ ≤ ‖J‖ * N₁ :=
    (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le J _).trans (mul_le_mul_of_nonneg_left
      ((OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα.le L L.isometry _).trans (hVN h hh hd)) (norm_nonneg J))
  have hFN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖F' h‖ ≤ Nf :=
    (OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα.le L L.isometry _).trans (hFN h hh hd)
  have hPD' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) (hy : y ∈ ball y₀ ρ) :
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) y).PosDef := OAI.Analysis.PDE.Dirichlet.matrixReindex_posDef e.symm (hPD h hh hd _ (hnear y hy))
  have heq' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) (hy : y ∈ ball y₀ ρ) :
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h)) (u' h) y = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F' h) y := by
    have ht := OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator_reindex e.symm (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h))
      (u h) (hu h hh hd) y
    exact ht.trans (heq h hh hd _ (hnear y hy))
  have hreg := elliptic_family_limit_C2 hm hα hα1 hρ hδ hM A' hA' y₀
    (OAI.Analysis.PDE.Dirichlet.matrixReindexCLM e.symm A₀) (OAI.Analysis.PDE.Dirichlet.matrixReindex_posDef e.symm hA₀) hAlim' u'
    (fun h hh hd => (hu h hh hd).comp L.contDiff) U' V' F' hU' hV' hUN' hVN' hFN' hPD' heq'
    (w ∘ L) (fun y => hw (L y))
  have hc := hreg.comp x₀ (OAI.Analysis.PDE.Dirichlet.coordinateReindex e).contDiff.contDiffAt
  have he : (w ∘ L) ∘ OAI.Analysis.PDE.Dirichlet.coordinateReindex e = w := by
    funext x
    exact congrArg w (OAI.Analysis.PDE.Dirichlet.coordinateReindex_symm_apply e x)
  simpa only [he] using hc

end OAI.Analysis.PDE.Nonlinear
