import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffForcing

/-! Bounded cutoff operators on the lower-order Hölder jets, independent of the unknown Hessian. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def cutoffFirstHolder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ)
    (hχc : HasCompactSupport χ) (v : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  compactC1Holder (fun x => fderiv ℝ χ x v)
    (((hχ.fderiv_right (m := 2) (by norm_num)).of_le (by norm_num)).clm_apply contDiff_const)
    (hχc.fderiv_apply ℝ v) hα hα1

@[simp] theorem cutoffFirstHolder_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ)
    (hχc : HasCompactSupport χ) (v x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffFirstHolder hα hα1 χ hχ hχc v) x = fderiv ℝ χ x v := rfl

def cutoffSecondHolder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ)
    (hχc : HasCompactSupport χ) (v w : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  compactC1Holder (fun x => fderiv ℝ (fderiv ℝ χ) x v w)
    ((((hχ.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).clm_apply contDiff_const)
    (by
      simpa only [Function.comp_def] using
        (((hχc.fderiv ℝ).fderiv_apply ℝ v).comp_left
          (g := fun l : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ => l w) rfl)) hα hα1

@[simp] theorem cutoffSecondHolder_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ)
    (hχc : HasCompactSupport χ) (v w x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffSecondHolder hα hα1 χ hχ hχc v w) x = fderiv ℝ (fderiv ℝ χ) x v w := rfl

def holderMultiply {E : Type*} [MetricSpace E] {α : ℝ} (hα : 0 ≤ α)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.bilinearCLM hα (ContinuousLinearMap.mul ℝ ℝ) a

@[simp] theorem holderMultiply_value {E : Type*} [MetricSpace E] {α : ℝ} (hα : 0 ≤ α)
    (a b : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderMultiply hα a b) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value a x * OAI.Analysis.Normed.Function.Holder.HolderMap.value b x := rfl

def matrixEntryHolder {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α) (i j : Fin m) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixEntryCLM i j) A

@[simp] theorem matrixEntryHolder_value {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (i j : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (matrixEntryHolder A i j) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j := rfl

def holderGradientEvaluation {m : ℕ} {α : ℝ} (v : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (ContinuousLinearMap.apply ℝ ℝ v)

@[simp] theorem holderGradientEvaluation_value {m : ℕ} {α : ℝ}
    (v x : EuclideanSpace ℝ (Fin m))
    (U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderGradientEvaluation v U) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value U x v := rfl

def cutoffValueOperator {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  ∑ i, ∑ j, (holderMultiply hα (matrixEntryHolder A i j)).comp
    (holderMultiply hα (cutoffSecondHolder hα hα1 χ hχ hχc (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)))

def cutoffGradientOperator {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α →L[ℝ]
      OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  ∑ i, ∑ j, (holderMultiply hα (matrixEntryHolder A i j)).comp
    ((holderMultiply hα (cutoffFirstHolder hα hα1 χ hχ hχc (EuclideanSpace.single i 1))).comp
      (holderGradientEvaluation (EuclideanSpace.single j 1)) +
    (holderMultiply hα (cutoffFirstHolder hα hα1 χ hχ hχc (EuclideanSpace.single j 1))).comp
      (holderGradientEvaluation (EuclideanSpace.single i 1)))

theorem cutoffValueOperator_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffValueOperator hα hα1 A χ hχ hχc U) x =
      ∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j *
        (fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * OAI.Analysis.Normed.Function.Holder.HolderMap.value U x) := by
  simp [cutoffValueOperator]

theorem cutoffGradientOperator_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (cutoffGradientOperator hα hα1 A χ hχ hχc V) x =
      ∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x i j *
        (fderiv ℝ χ x (EuclideanSpace.single i 1) * OAI.Analysis.Normed.Function.Holder.HolderMap.value V x (EuclideanSpace.single j 1) +
         fderiv ℝ χ x (EuclideanSpace.single j 1) * OAI.Analysis.Normed.Function.Holder.HolderMap.value V x (EuclideanSpace.single i 1)) := by
  simp [cutoffGradientOperator, mul_add]

end OAI.Analysis.PDE.Schauder
