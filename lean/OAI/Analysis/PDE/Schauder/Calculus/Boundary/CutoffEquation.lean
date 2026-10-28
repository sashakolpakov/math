import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformCutoff

/-! The cutoff equation only uses the jets at the evaluation point. In particular,
arbitrary extensions across the flat boundary do not alter it on the halfspace. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem cutoffJetForcing_equation_at {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hu : ContDiff ℝ 2 u) (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (x : EuclideanSpace ℝ (Fin m))
    (hU : OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) (hV : OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (heq : χ x ≠ 0 → nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) :
    nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (fun y => χ y * u y) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffJetForcing hα hα1 A χ hχ hχc F U V) x := by
  rw [nondivergence_cutoff (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) χ u (hχ.of_le (by norm_num)) hu,
    cutoffJetForcing_value]
  simp only [hU, hV, cutoffCommutatorEntry]
  congr 1
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul]
  · rw [heq hx]

end OAI.Analysis.PDE.Schauder
