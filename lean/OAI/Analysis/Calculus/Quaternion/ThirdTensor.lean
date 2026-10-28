import OAI.Analysis.Calculus.Quaternion.Polarization

/-! Cubic symbol cancellation implies cancellation against symmetric third tensors. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module ℝ W]

def coefficientTrilinear (C : ι → ι → ι → W) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] W :=
  ∑ i, ∑ j, ∑ k, (LinearMap.proj i).smulRight
    ((LinearMap.proj j).smulRight ((LinearMap.proj k).smulRight (C i j k)))

omit [DecidableEq ι] in
theorem coefficientTrilinear_apply (C : ι → ι → ι → W) (x y z : ι → ℝ) :
    coefficientTrilinear C x y z = ∑ i, ∑ j, ∑ k, (x i * y j * z k) • C i j k := by
  simp [coefficientTrilinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, smul_smul, mul_assoc]

theorem coefficientTrilinear_single (C : ι → ι → ι → W) (i j k : ι) :
    coefficientTrilinear C (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) = C i j k := by
  simp [coefficientTrilinear_apply, Pi.single_apply]

theorem linearMap_matrix_expansion (L : Matrix ι ι ℝ →ₗ[ℝ] W) (A : Matrix ι ι ℝ) :
    L A = ∑ i, ∑ j, A i j • L (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  congr 1
  ext i
  congr 1
  ext j
  rw [← map_smul]
  congr 1
  simp

theorem coefficientTrilinear_diagonal (L : ι → Matrix ι ι ℝ →ₗ[ℝ] W)
    (x : ι → ℝ) :
    coefficientTrilinear (fun i j k => L i (Matrix.single j k 1)) x x x =
      ∑ i, x i • L i (fun j k => x j * x k) := by
  rw [coefficientTrilinear_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [linearMap_matrix_expansion (L i) (fun j k => x j * x k)]
  simp only [Finset.smul_sum, smul_smul, mul_assoc]

/-- A cubic rank-one identity suffices for an arbitrary symmetric third tensor. -/
theorem symmetric_third_tensor_cancellation
    (L : ι → Matrix ι ι ℝ →ₗ[ℝ] W)
    (hL : ∀ x : ι → ℝ, ∑ i, x i • L i (fun j k => x j * x k) = 0)
    (T : ι → ι → ι → ℝ)
    (h12 : ∀ i j k, T i j k = T j i k)
    (h23 : ∀ i j k, T i j k = T i k j) :
    ∑ i, L i (T i) = 0 := by
  have hB (x : ι → ℝ) :
      coefficientTrilinear (fun i j k => L i (Matrix.single j k 1)) x x x = 0 := by
    rw [coefficientTrilinear_diagonal, hL]
  have h := trilinear_symmetric_contraction_zero
    (coefficientTrilinear (fun i j k => L i (Matrix.single j k 1))) hB
    (fun i => Pi.single i 1) T h12 h23
  simp only [coefficientTrilinear_single, cubicContraction] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  exact linearMap_matrix_expansion (L i) (T i)

end OAI.Analysis.Calculus.Quaternion
