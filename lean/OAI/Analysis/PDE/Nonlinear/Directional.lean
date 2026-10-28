import OAI.Analysis.PDE.Nonlinear.NormalizedLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceCalculus

/-! The normalized nonlinear bootstrap, with only C²,α lower jets assumed. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

theorem directional_C2At_of_normalized_family {m : ℕ} (hm : 3 ≤ m) {α ρ δ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (OAI.Analysis.PDE.Schauder.EuclideanHessian m) α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ f x)
    (v x₀ : EuclideanSpace ℝ (Fin m))
    (A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hA : ∀ h, ‖A h‖ ≤ M)
    (hAlim : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) (𝓝 0) (𝓝 1))
    (hPD : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x).PosDef)
    (heq : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ,
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
        OAI.Analysis.PDE.Weak.differenceQuotient v h f x) :
    ContDiffAt ℝ 2 (fun x => fderiv ℝ u x v) x₀ := by
  classical
  let Uₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le u (hu.of_le (by norm_num)) V hV v hh
  let Vₕ (h : ℝ) := if hh : h = 0 then
    (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le (fderiv ℝ u) (hu.fderiv_right (m := 1) (by norm_num)) H hH v hh
  let Fₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le f hf D hD v hh
  have hUv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Uₕ h) x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := by
    simp only [Uₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
  have hVv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Vₕ h) x =
      fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x := by
    simp only [Vₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
    exact (OAI.Analysis.PDE.Schauder.fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h x).symm
  have hFv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Fₕ h) x = OAI.Analysis.PDE.Weak.differenceQuotient v h f x := by
    simp only [Fₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
  apply normalized_family_limit_C2 hm hα hα1 hρ hδ hM A hA x₀ hAlim
    (fun h => OAI.Analysis.PDE.Weak.differenceQuotient v h u) (fun h _ _ => OAI.Analysis.PDE.Schauder.contDiff_differenceQuotient u hu v h)
    Uₕ Vₕ Fₕ (fun h hh _ => hUv h hh) (fun h hh _ => hVv h hh)
    (N₀ := ‖V‖ * ‖v‖) (N₁ := ‖H‖ * ‖v‖) (Nf := ‖D‖ * ‖v‖)
  · intro h hh _
    simp only [Uₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le u _ V hV v hh
  · intro h hh _
    simp only [Vₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le (fderiv ℝ u) _ H hH v hh
  · intro h hh _
    simp only [Fₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le f _ D hD v hh
  · exact hPD
  · intro h hh hd x hx
    rw [hFv h hh x]
    exact heq h hh hd x hx
  · intro x
    exact OAI.Analysis.PDE.Schauder.tendsto_differenceQuotient u v x (hu.differentiable (by norm_num) x)

end OAI.Analysis.PDE.Nonlinear
