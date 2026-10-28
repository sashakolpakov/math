import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Congruence

/-! Hölder fields under arbitrary affine coordinate changes. -/

noncomputable section
open Set Metric Matrix
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def holderLinearAffinePullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}
    (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (L : E →L[ℝ] E) : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := by
  let φ : C(E, E) := ⟨fun x => x₀ + L x, continuous_const.add L.continuous⟩
  let b : E →ᵇ F := (OAI.Analysis.Normed.Function.Holder.HolderMap.value f).compContinuous φ
  refine OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b (C := ‖f‖ * ‖L‖ ^ α) ?_
  intro x y
  change ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + L x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + L y)‖ ≤ _
  have he : x₀ + L x - (x₀ + L y) = L (x - y) := by rw [map_sub]; abel
  have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (x₀ + L x) (x₀ + L y)
  rw [dist_eq_norm, he] at h
  rw [dist_eq_norm]
  calc
    _ ≤ ‖f‖ * ‖L (x - y)‖ ^ α := h
    _ ≤ ‖f‖ * (‖L‖ * ‖x - y‖) ^ α :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (L.le_opNorm _) hα) (norm_nonneg _)
    _ = _ := by rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]; ring

@[simp] theorem holderLinearAffinePullback_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (L : E →L[ℝ] E) (x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderLinearAffinePullback hα f x₀ L) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + L x) := rfl

theorem matrix_congruence_cancel {m : ℕ} (P Q A : Matrix (Fin m) (Fin m) ℝ)
    (hPQ : P * Q = 1) : P * (Q * A * Q.transpose) * P.transpose = A := by
  calc
    _ = (P * Q) * A * (P * Q).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [hPQ, Matrix.transpose_one, one_mul, mul_one]

theorem nondivergence_conjugated_affine {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (P Q : Matrix (Fin m) (Fin m) ℝ) (hPQ : P * Q = 1)
    (x₀ x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator
      (fun y => Q * A (x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P y) * Q.transpose)
      (fun y => u (x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P y)) x =
      nondivergenceOperator A u (x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P x) := by
  rw [nondivergence_comp_affine_matrix _ u hu P]
  simp only [matrix_congruence_cancel P Q _ hPQ, nondivergenceOperator]

theorem exists_normalization_matrices {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) :
    ∃ (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (P Q : Matrix (Fin m) (Fin m) ℝ),
      Matrix.toEuclideanCLM (𝕜 := ℝ) P = L.toContinuousLinearMap ∧
      Matrix.toEuclideanCLM (𝕜 := ℝ) Q = L.symm.toContinuousLinearMap ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * A * Q.transpose = 1 := by
  obtain ⟨L, hL, _⟩ := exists_elliptic_normalization A hA
  let P := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L.toContinuousLinearMap
  let Q := (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).symm L.symm.toContinuousLinearMap
  have hP : Matrix.toEuclideanCLM (𝕜 := ℝ) P = L.toContinuousLinearMap :=
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).apply_symm_apply _
  have hQ : Matrix.toEuclideanCLM (𝕜 := ℝ) Q = L.symm.toContinuousLinearMap :=
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).apply_symm_apply _
  have hPQ : P * Q = 1 := by
    apply (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) P * Matrix.toEuclideanCLM (𝕜 := ℝ) Q = 1
    rw [hP, hQ]
    apply ContinuousLinearMap.ext
    intro x
    exact L.apply_symm_apply x
  have hQP : Q * P = 1 := by
    apply (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) Q * Matrix.toEuclideanCLM (𝕜 := ℝ) P = 1
    rw [hP, hQ]
    apply ContinuousLinearMap.ext
    intro x
    exact L.symm_apply_apply x
  have hAeq : A = P * P.transpose := by
    rw [← hL, ← hP, linearEllipticMatrix_toEuclideanCLM]
  refine ⟨L, P, Q, hP, hQ, hPQ, hQP, ?_⟩
  rw [hAeq]
  calc
    _ = (Q * P) * (Q * P).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hQP, Matrix.transpose_one, mul_one]

end OAI.Analysis.PDE.Schauder
