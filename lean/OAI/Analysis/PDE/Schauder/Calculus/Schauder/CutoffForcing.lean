import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffEquation

/-! A concrete Hölder-space representative of the localized forcing. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def matrixEntryCLM {m : ℕ} (i j : Fin m) : Matrix (Fin m) (Fin m) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin m → Fin m → ℝ) →L[ℝ] (Fin m → ℝ))

@[simp] theorem matrixEntryCLM_apply {m : ℕ} (i j : Fin m) (A : Matrix (Fin m) (Fin m) ℝ) :
    matrixEntryCLM i j A = A i j := rfl

def cutoffForcing {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ 2 u) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.mul ℝ ℝ)
      (compactC1Holder χ (hχ.of_le (by norm_num)) hχc hα hα1) F +
    ∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.mul ℝ ℝ)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixEntryCLM i j) A)
      (compactC1Holder
        (cutoffCommutatorEntry χ u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        (contDiff_cutoffCommutatorEntry χ u hχ hu _ _)
        (hasCompactSupport_cutoffCommutatorEntry χ u hχc _ _) hα hα1)

theorem cutoffForcing_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffForcing hα hα1 A F χ u hχ hχc hu) x =
      χ x * OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + ∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j *
        cutoffCommutatorEntry χ u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x := by
  simp [cutoffForcing]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

theorem cutoffForcing_equation {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ 2 u)
    (heq : ∀ x ∈ Function.support χ, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x)
    (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (fun y => χ y * u y) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffForcing hα hα1 A F χ u hχ hχc hu) x := by
  rw [cutoffForcing_value, nondivergence_cutoff _ χ u (hχ.of_le (by norm_num)) hu]
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul]
  · rw [heq x hx]

theorem cutoffCommutatorEntry_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ u : E → ℝ) (v w x : E) (hx : x ∉ tsupport χ) :
    cutoffCommutatorEntry χ u v w x = 0 := by
  have hD : fderiv ℝ χ x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ h)
  have hDD : fderiv ℝ (fderiv ℝ χ) x = 0 := by
    by_contra h
    exact hx (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
  simp [cutoffCommutatorEntry, hD, hDD]

theorem cutoffForcing_zero {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (χ u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) (hu : ContDiff ℝ 2 u)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∉ tsupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffForcing hα hα1 A F χ u hχ hχc hu) x = 0 := by
  rw [cutoffForcing_value]
  have hc : χ x = 0 := by
    by_contra h
    exact hx (subset_closure h)
  simp [hc, cutoffCommutatorEntry_zero χ u _ _ x hx]

end OAI.Analysis.PDE.Schauder
