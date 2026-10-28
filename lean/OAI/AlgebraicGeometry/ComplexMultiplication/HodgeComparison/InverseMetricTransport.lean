import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence

/-! # Inverse Metric Transport -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetricTransport.CM.Construction

noncomputable section

/-! Inverse-metric derivatives inherit the Kähler symmetry after raising
the differentiating index. -/

theorem inverse_metric_transport_symmetric {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (P : Matrix ι ι R) (A : ι → Matrix ι ι R)
    (hA : ∀ i j k, A i j k = A j i k) (a j k : ι) :
    (∑ d, P a d * (P * A d * P) j k) = ∑ d, P j d * (P * A d * P) a k := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ d, ∑ m, ∑ l, P a d * (P j l * A l d m * P m k) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro l _
      rw [hA d l m]
    _ = ∑ d, ∑ l, ∑ m, P a d * (P j l * A l d m * P m k) := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ l, ∑ d, ∑ m, P a d * (P j l * A l d m * P m k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro d _
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem antiholomorphicDirectionalDerivative_mul (f g : E → ℂ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => f y * g y) x u =
      f x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u +
      g x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative f x u := by
  simp only [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixAntiholomorphicDerivative (M : E → Matrix ι ι ℂ) (x u : E) : Matrix ι ι ℂ :=
  Matrix.of fun i j => AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => M y i j) x u

omit [Fintype ι] [DecidableEq ι] in
theorem matrixAntiholomorphicDerivative_eq (M : E → Matrix ι ι ℂ) (x u : E) :
    matrixAntiholomorphicDerivative M x u = (1 / 2 : ℂ) •
      (HolomorphicMatrixCalculus.CM.Construction.matrixDirectionalDerivative M x u + Complex.I •
        HolomorphicMatrixCalculus.CM.Construction.matrixDirectionalDerivative M x (Complex.I • u)) := by
  ext i j
  rfl

theorem antiholomorphic_matrix_inverse (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (u : E) :
    matrixAntiholomorphicDerivative (fun y => (M y)⁻¹) x u =
      -((M x)⁻¹ * matrixAntiholomorphicDerivative M x u * (M x)⁻¹) := by
  rw [matrixAntiholomorphicDerivative_eq, HolomorphicMatrixCalculus.CM.Construction.matrix_directional_inverse M hM hdet,
    HolomorphicMatrixCalculus.CM.Construction.matrix_directional_inverse M hM hdet, matrixAntiholomorphicDerivative_eq]
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, Matrix.add_mul]
  module

theorem antiholomorphic_inverse_transport_symmetric (M : E → Matrix ι ι ℂ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x)
    (hdet : IsUnit (M x).det) (v : ι → E)
    (hK : ∀ i j k, matrixAntiholomorphicDerivative M x (v i) j k =
      matrixAntiholomorphicDerivative M x (v j) i k) (a j k : ι) :
    (∑ d, (M x)⁻¹ a d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => (M y)⁻¹ j k) x (v d)) =
      ∑ d, (M x)⁻¹ j d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => (M y)⁻¹ a k) x (v d) := by
  have hi (d r s : ι) : AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => (M y)⁻¹ r s) x (v d) =
      -((M x)⁻¹ * matrixAntiholomorphicDerivative M x (v d) * (M x)⁻¹) r s :=
    congrArg (fun P : Matrix ι ι ℂ => P r s) (antiholomorphic_matrix_inverse M hM hdet (v d))
  simp only [hi, mul_neg, Finset.sum_neg_distrib]
  congr 1
  exact inverse_metric_transport_symmetric _ _ hK a j k

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetricTransport.CM.Construction
