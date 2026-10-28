import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffOperators

/-! The localized right-hand side is bounded by the lower-order Hölder jets. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def cutoffJetForcing {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  holderMultiply hα (compactC1Holder χ (hχ.of_le (by norm_num)) hχc hα hα1) F +
    cutoffValueOperator hα hα1 A χ hχ hχc U + cutoffGradientOperator hα hα1 A χ hχ hχc V

theorem cutoffJetForcing_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffJetForcing hα hα1 A χ hχ hχc F U V) x =
      χ x * OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + ∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j *
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value U x * fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
          fderiv ℝ χ x (EuclideanSpace.single i 1) * OAI.Analysis.Normed.Function.Holder.HolderMap.value V x (EuclideanSpace.single j 1) +
          OAI.Analysis.Normed.Function.Holder.HolderMap.value V x (EuclideanSpace.single i 1) * fderiv ℝ χ x (EuclideanSpace.single j 1)) := by
  simp only [cutoffJetForcing, OAI.Analysis.Normed.Function.Holder.HolderMap.value_add, BoundedContinuousFunction.add_apply,
    holderMultiply_value, compactC1Holder_value, cutoffValueOperator_value, cutoffGradientOperator_value]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem cutoffJetForcing_bound {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    ∃ C > 0, ∀ (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
      (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      ‖cutoffJetForcing hα hα1 A χ hχ hχc F U V‖ ≤ C * (‖F‖ + ‖U‖ + ‖V‖) := by
  let T := holderMultiply hα (compactC1Holder χ (hχ.of_le (by norm_num)) hχc hα hα1)
  let S := cutoffValueOperator hα hα1 A χ hχ hχc
  let P := cutoffGradientOperator hα hα1 A χ hχ hχc
  let C := ‖T‖ + ‖S‖ + ‖P‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro F U V
  change ‖T F + S U + P V‖ ≤ _
  calc
    _ ≤ ‖T F‖ + ‖S U‖ + ‖P V‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖T‖ * ‖F‖ + ‖S‖ * ‖U‖ + ‖P‖ * ‖V‖ :=
      add_le_add (add_le_add (T.le_opNorm _) (S.le_opNorm _)) (P.le_opNorm _)
    _ ≤ C * ‖F‖ + C * ‖U‖ + C * ‖V‖ := by
      apply add_le_add
      · apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
          dsimp only [C]; linarith [norm_nonneg S, norm_nonneg P]
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg U)
          dsimp only [C]; linarith [norm_nonneg T, norm_nonneg P]
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg V)
        dsimp only [C]; linarith [norm_nonneg T, norm_nonneg S]
    _ = _ := by ring

theorem cutoffJetForcing_equation {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hu : ContDiff ℝ 2 u) (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hU : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (heq : ∀ x ∈ Function.support χ, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x)
    (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (fun y => χ y * u y) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffJetForcing hα hα1 A χ hχ hχc F U V) x := by
  rw [cutoffForcing_equation hα hα1 A F χ u hχ hχc hu heq x,
    cutoffForcing_value, cutoffJetForcing_value]
  simp only [hU, hV, cutoffCommutatorEntry]

theorem cutoffJetForcing_zero {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∉ tsupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffJetForcing hα hα1 A χ hχ hχc F U V) x = 0 := by
  have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hD : fderiv ℝ χ x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ h)
  have hDD : fderiv ℝ (fderiv ℝ χ) x = 0 := by
    by_contra h
    exact hx (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
  simp [cutoffJetForcing_value, hc, hD, hDD]

end OAI.Analysis.PDE.Schauder
