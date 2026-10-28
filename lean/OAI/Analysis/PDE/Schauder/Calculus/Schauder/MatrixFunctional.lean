import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Coefficient
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation
import OAI.Analysis.Normed.Function.Holder.Banach.Linear

/-! Real matrix coefficients as bounded functionals on the genuine Fréchet Hessian. -/

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

local instance functionalMatrixNormedGroup (m : ℕ) :
    NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance functionalMatrixNormedSpace (m : ℕ) :
    NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

def matrixHessianFunctional {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    EuclideanHessian m →L[ℝ] ℝ :=
  LinearMap.mkContinuous {
    toFun B := ∑ i : Fin m, ∑ j : Fin m,
      A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    map_add' := by
      intro B C
      simp only [add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c B
      simp only [smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring }
    (∑ i : Fin m, ∑ j : Fin m, |A i j|) (by
      intro B
      change |∑ i : Fin m, ∑ j : Fin m,
        A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ _
      calc
        _ ≤ ∑ i : Fin m, ∑ j : Fin m,
            |A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
        _ ≤ ∑ i : Fin m, ∑ j : Fin m, |A i j| * ‖B‖ := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (euclidean_bilinear_entry_le_norm B i j) (abs_nonneg _)
        _ = _ := by simp only [Finset.sum_mul])

theorem matrixHessianFunctional_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (B : EuclideanHessian m) :
    matrixHessianFunctional A B = ∑ i : Fin m, ∑ j : Fin m,
      A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := rfl

theorem norm_matrixHessianFunctional_le {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    ‖matrixHessianFunctional A‖ ≤ (m : ℝ) * m * ‖A‖ := by
  have hb : ‖matrixHessianFunctional A‖ ≤ ∑ i : Fin m, ∑ j : Fin m, |A i j| :=
    LinearMap.mkContinuous_norm_le _ (by positivity) _
  apply hb.trans
  calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Matrix.norm_entry_le_entrywise_sup_norm A
    _ = _ := by simp; ring

def matrixHessianFunctionalCLM (m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ →L[ℝ] (EuclideanHessian m →L[ℝ] ℝ) :=
  LinearMap.mkContinuous {
    toFun := matrixHessianFunctional
    map_add' := by
      intro A B
      ext H
      simp only [matrixHessianFunctional_apply, Matrix.add_apply, add_mul,
        add_apply, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      ext H
      simp only [matrixHessianFunctional_apply, Matrix.smul_apply, smul_eq_mul,
        RingHom.id_apply, smul_apply, Finset.mul_sum, mul_assoc] }
    ((m : ℝ) * m) norm_matrixHessianFunctional_le

def matrixCoefficientField {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m →L[ℝ] ℝ) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (matrixHessianFunctionalCLM m) A

theorem norm_matrixCoefficientField_le {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α) :
    ‖matrixCoefficientField A‖ ≤ (m : ℝ) * m * ‖A‖ := by
  change max ‖(matrixHessianFunctionalCLM m).compLeftContinuousBounded _ A.val.1‖
    ‖(matrixHessianFunctionalCLM m).compLeftContinuousBounded _ A.val.2‖ ≤ _
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖matrixHessianFunctional (A.val.1 x)‖ ≤ _
    exact (norm_matrixHessianFunctional_le _).trans
      (mul_le_mul_of_nonneg_left (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le A x) (by positivity))
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro q
    change ‖matrixHessianFunctional (A.val.2 q)‖ ≤ _
    exact (norm_matrixHessianFunctional_le _).trans
      (mul_le_mul_of_nonneg_left
        ((A.val.2.norm_coe_le_norm q).trans (le_max_right _ _)) (by positivity))

theorem matrixCoefficientField_zero {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (x : EuclideanSpace ℝ (Fin m)) (hx : OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (matrixCoefficientField A) x = 0 := by
  change matrixHessianFunctionalCLM m (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) = 0
  rw [hx, map_zero]

theorem matrixCoefficientField_apply {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (matrixCoefficientField A) x (fderiv ℝ (fderiv ℝ u) x) =
      nondivergenceOperator (fun y => OAI.Analysis.Normed.Function.Holder.HolderMap.value A y) u x := rfl

end OAI.Analysis.PDE.Schauder
