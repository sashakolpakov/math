import OAI.Analysis.PDE.Schauder.Calculus.Schauder.JetForcing

/-! The cutoff operators depend bounded-linearly on the coefficient field. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

private abbrev ScalarHolder (m : ℕ) (α : ℝ) := OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α
private abbrev GradientHolder (m : ℕ) (α : ℝ) :=
  OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α
private abbrev MatrixHolder (m : ℕ) (α : ℝ) :=
  OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α

local instance uniformMatrixNG (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance uniformMatrixNS (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance uniformGradientNG (m : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance uniformGradientNS (m : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance uniformScalarHolderNG (m : ℕ) (α : ℝ) : NormedAddCommGroup (ScalarHolder m α) := inferInstance
local instance uniformScalarHolderNS (m : ℕ) (α : ℝ) : NormedSpace ℝ (ScalarHolder m α) := inferInstance
local instance uniformGradientHolderNG (m : ℕ) (α : ℝ) : NormedAddCommGroup (GradientHolder m α) := inferInstance
local instance uniformGradientHolderNS (m : ℕ) (α : ℝ) : NormedSpace ℝ (GradientHolder m α) := inferInstance
local instance uniformMatrixHolderNG (m : ℕ) (α : ℝ) : NormedAddCommGroup (MatrixHolder m α) := inferInstance
local instance uniformMatrixHolderNS (m : ℕ) (α : ℝ) : NormedSpace ℝ (MatrixHolder m α) := inferInstance
local instance uniformScalarOperatorNG (m : ℕ) (α : ℝ) :
    NormedAddCommGroup (ScalarHolder m α →L[ℝ] ScalarHolder m α) := inferInstance
local instance uniformScalarOperatorNS (m : ℕ) (α : ℝ) :
    NormedSpace ℝ (ScalarHolder m α →L[ℝ] ScalarHolder m α) := inferInstance
local instance uniformGradientOperatorNG (m : ℕ) (α : ℝ) :
    NormedAddCommGroup (GradientHolder m α →L[ℝ] ScalarHolder m α) := inferInstance
local instance uniformGradientOperatorNS (m : ℕ) (α : ℝ) :
    NormedSpace ℝ (GradientHolder m α →L[ℝ] ScalarHolder m α) := inferInstance

def cutoffValueCoefficientOperator {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α →L[ℝ]
      (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) := by
  let H := OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α
  exact ∑ i, ∑ j,
    ((ContinuousLinearMap.compL ℝ H H H).flip
      (holderMultiply hα (cutoffSecondHolder hα hα1 χ hχ hχc
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))).comp
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.bilinearCLM hα (ContinuousLinearMap.mul ℝ ℝ)).comp
        (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixEntryCLM i j)))

theorem cutoffValueCoefficientOperator_apply {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α) :
    cutoffValueCoefficientOperator hα hα1 χ hχ hχc A = cutoffValueOperator hα hα1 A χ hχ hχc := by
  simp [cutoffValueCoefficientOperator, cutoffValueOperator, holderMultiply, matrixEntryHolder]

def cutoffGradientCoefficientOperator {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α →L[ℝ]
      (OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α →L[ℝ]
        OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) := by
  let H := OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α
  let G := OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α
  exact ∑ i, ∑ j,
    ((ContinuousLinearMap.compL ℝ G H H).flip
      ((holderMultiply hα (cutoffFirstHolder hα hα1 χ hχ hχc (EuclideanSpace.single i 1))).comp
        (holderGradientEvaluation (EuclideanSpace.single j 1)) +
       (holderMultiply hα (cutoffFirstHolder hα hα1 χ hχ hχc (EuclideanSpace.single j 1))).comp
        (holderGradientEvaluation (EuclideanSpace.single i 1)))).comp
      ((OAI.Analysis.Normed.Function.Holder.HolderMap.bilinearCLM hα (ContinuousLinearMap.mul ℝ ℝ)).comp
        (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixEntryCLM i j)))

theorem cutoffGradientCoefficientOperator_apply {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α) :
    cutoffGradientCoefficientOperator hα hα1 χ hχ hχc A = cutoffGradientOperator hα hα1 A χ hχ hχc := by
  simp [cutoffGradientCoefficientOperator, cutoffGradientOperator, holderMultiply, matrixEntryHolder]

theorem cutoffJetForcing_uniform_bound {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    ∃ C > 0, ∀ (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
      (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
      (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      ‖cutoffJetForcing hα hα1 A χ hχ hχc F U V‖ ≤
        C * (‖F‖ + ‖A‖ * (‖U‖ + ‖V‖)) := by
  let T := holderMultiply hα (compactC1Holder χ (hχ.of_le (by norm_num)) hχc hα hα1)
  let S := cutoffValueCoefficientOperator hα hα1 χ hχ hχc
  let P := cutoffGradientCoefficientOperator hα hα1 χ hχ hχc
  let C := ‖T‖ + ‖S‖ + ‖P‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have ht : ‖T‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg S, norm_nonneg P]
  have hs : ‖S‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg T, norm_nonneg P]
  have hp : ‖P‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg T, norm_nonneg S]
  refine ⟨C, hC, ?_⟩
  intro A F U V
  have hv : ‖cutoffValueOperator hα hα1 A χ hχ hχc U‖ ≤ C * ‖A‖ * ‖U‖ := by
    rw [← cutoffValueCoefficientOperator_apply]
    exact ((S A).le_opNorm U).trans (mul_le_mul_of_nonneg_right
      ((S.le_opNorm A).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg A))) (norm_nonneg U))
  have hg : ‖cutoffGradientOperator hα hα1 A χ hχ hχc V‖ ≤ C * ‖A‖ * ‖V‖ := by
    rw [← cutoffGradientCoefficientOperator_apply]
    exact ((P A).le_opNorm V).trans (mul_le_mul_of_nonneg_right
      ((P.le_opNorm A).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg A))) (norm_nonneg V))
  have hf : ‖T F‖ ≤ C * ‖F‖ := (T.le_opNorm F).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg F))
  calc
    _ ≤ ‖T F‖ + ‖cutoffValueOperator hα hα1 A χ hχ hχc U‖ +
        ‖cutoffGradientOperator hα hα1 A χ hχ hχc V‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * ‖F‖ + C * ‖A‖ * ‖U‖ + C * ‖A‖ * ‖V‖ := add_le_add (add_le_add hf hv) hg
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
