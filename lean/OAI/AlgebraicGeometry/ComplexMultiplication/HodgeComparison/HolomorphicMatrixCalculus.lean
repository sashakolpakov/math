import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DeterminantDerivative

/-! # Holomorphic Matrix Calculus -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMatrixCalculus.CM.Construction

noncomputable section

section

/-! Entrywise differentiation of the actual nonsingular matrix inverse. -/

open Filter
open scoped _root_.Topology

variable {ι 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def matrixDirectionalDerivative (M : E → Matrix ι ι 𝕜) (x u : E) : Matrix ι ι 𝕜 :=
  Matrix.of fun i j => fderiv ℝ (fun y => M y i j) x u

theorem matrix_determinant_differentiableAt (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  fun_prop

theorem matrix_inverse_differentiableAt (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (i j : ι) :
    DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := by
  have hd := matrix_determinant_differentiableAt M hM
  have ha : DifferentiableAt ℝ (fun y => (M y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply matrix_determinant_differentiableAt
    intro a b
    by_cases hab : a = j
    · simp only [Matrix.updateRow_apply, hab, ite_true]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_apply, hab, ite_false]
      exact hM a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (hd.inv hdet.ne_zero).mul ha

omit [DecidableEq ι] in
theorem matrix_directional_product (M N : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hN : ∀ i j, DifferentiableAt ℝ (fun y => N y i j) x) (u : E) :
    matrixDirectionalDerivative (fun y => M y * N y) x u =
      M x * matrixDirectionalDerivative N x u + matrixDirectionalDerivative M x u * N x := by
  ext i j
  simp only [matrixDirectionalDerivative, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => M y i k * N y k j)
    (fun k _ => (hM i k).mul (hN k j)), sum_apply]
  simp only [fderiv_fun_mul (hM _ _) (hN _ _), add_apply, smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem matrix_directional_inverse (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) :
    matrixDirectionalDerivative (fun y => (M y)⁻¹) x u =
      -((M x)⁻¹ * matrixDirectionalDerivative M x u * (M x)⁻¹) := by
  have hnear : ∀ᶠ y in 𝓝 x, IsUnit (M y).det := by
    filter_upwards [(matrix_determinant_differentiableAt M hM).continuousAt.eventually_ne
      hdet.ne_zero] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have hzero : matrixDirectionalDerivative (fun y => (M y)⁻¹ * M y) x u = 0 := by
    ext i j
    have heq : (fun y => ((M y)⁻¹ * M y) i j) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix ι ι 𝕜) i j) := by
      filter_upwards [hnear] with y hy
      rw [Matrix.nonsing_inv_mul _ hy]
    change fderiv ℝ (fun y => ((M y)⁻¹ * M y) i j) x u = 0
    rw [heq.fderiv_eq, fderiv_const_apply, zero_apply]
  rw [matrix_directional_product _ _ (matrix_inverse_differentiableAt M hM hdet) hM] at hzero
  have hm := congrArg (fun A : Matrix ι ι 𝕜 => A * (M x)⁻¹) hzero
  rw [add_mul, Matrix.mul_assoc (matrixDirectionalDerivative _ x u),
    Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.zero_mul] at hm
  exact eq_neg_of_add_eq_zero_right hm

theorem determinant_directional_trace (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) :
    fderiv ℝ (fun y => (M y).det) x u =
      (M x).det * ((M x)⁻¹ * matrixDirectionalDerivative M x u).trace := by
  rw [DeterminantDerivative.CM.Construction.determinant_derivative_trace M (fun i => differentiableAt_pi.mpr (hM i)) hdet]
  congr 3
  ext i j
  simp only [Matrix.of_apply, matrixDirectionalDerivative, fderiv_pi (hM i),
    ContinuousLinearMap.pi_apply]

end

/-! Holomorphic directional derivatives of determinant-weighted inverse coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem holomorphicDirectionalDerivative_mul (f g : E → ℂ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => f y * g y) x u =
      f x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u +
      g x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative f x u := by
  simp only [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixHolomorphicDerivative (M : E → Matrix ι ι ℂ) (x u : E) : Matrix ι ι ℂ :=
  Matrix.of fun i j => MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => M y i j) x u

omit [Fintype ι] [DecidableEq ι] in
theorem matrixHolomorphicDerivative_eq (M : E → Matrix ι ι ℂ) (x u : E) :
    matrixHolomorphicDerivative M x u = (1 / 2 : ℂ) •
      (matrixDirectionalDerivative M x u - Complex.I •
        matrixDirectionalDerivative M x (Complex.I • u)) := by
  ext i j
  rfl

theorem holomorphic_determinant_trace (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y).det) x u =
      (M x).det * ((M x)⁻¹ * matrixHolomorphicDerivative M x u).trace := by
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, determinant_directional_trace M hM hdet,
    determinant_directional_trace M hM hdet, matrixHolomorphicDerivative_eq]
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  ring

theorem holomorphic_matrix_inverse (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) :
    matrixHolomorphicDerivative (fun y => (M y)⁻¹) x u =
      -((M x)⁻¹ * matrixHolomorphicDerivative M x u * (M x)⁻¹) := by
  rw [matrixHolomorphicDerivative_eq, matrix_directional_inverse M hM hdet,
    matrix_directional_inverse M hM hdet, matrixHolomorphicDerivative_eq]
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul]
  module

theorem holomorphic_weighted_inverse_derivative (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) (i k : ι) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y).det * (M y)⁻¹ i k) x u =
      (M x).det * (((M x)⁻¹ * matrixHolomorphicDerivative M x u).trace * (M x)⁻¹ i k -
        ((M x)⁻¹ * matrixHolomorphicDerivative M x u * (M x)⁻¹) i k) := by
  rw [holomorphicDirectionalDerivative_mul _ _ (matrix_determinant_differentiableAt M hM)
    (matrix_inverse_differentiableAt M hM hdet i k), holomorphic_determinant_trace M hM hdet]
  have hi := congrArg (fun A : Matrix ι ι ℂ => A i k) (holomorphic_matrix_inverse M hM hdet u)
  change MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y)⁻¹ i k) x u =
    -((M x)⁻¹ * matrixHolomorphicDerivative M x u * (M x)⁻¹) i k at hi
  rw [hi]
  ring

theorem holomorphic_weighted_inverse_divergence (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (v : ι → E)
    (hK : ∀ i j k, matrixHolomorphicDerivative M x (v i) j k =
      matrixHolomorphicDerivative M x (v k) j i) (k : ι) :
    ∑ i, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => (M y).det * (M y)⁻¹ i k) x (v i) = 0 := by
  simp_rw [holomorphic_weighted_inverse_derivative M hM hdet]
  rw [← Finset.mul_sum, InverseCoefficientCancellation.CM.Construction.kahler_inverse_coefficient_cancellation _ _ hK, mul_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMatrixCalculus.CM.Construction
