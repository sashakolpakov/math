import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra

/-! # Two Density -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoDensity.Closedness

noncomputable section

section

/-! Skew symmetry cancels the Kähler metric derivatives in the (2,0) flux. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction

variable {ι : Type*} [Fintype ι]

theorem skew_two_flux_metric_derivative_zero (P S : Matrix ι ι ℂ)
    (DP : ι → Matrix ι ι ℂ)
    (hP : ∀ a k j, (∑ d, P a d * DP d k j) = ∑ d, P k d * DP d a j)
    (hS : ∀ a k, S k a = -S a k) (j : ι) :
    (∑ d, ∑ a, ∑ k, P a d * DP d k j * S a k) = 0 := by
  let T := ∑ a, ∑ k, (∑ d, P a d * DP d k j) * S a k
  have heq : (∑ d, ∑ a, ∑ k, P a d * DP d k j * S a k) = T := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
  have hneg : T = -T := by
    calc
      T = ∑ k, ∑ a, (∑ d, P a d * DP d k j) * S a k := Finset.sum_comm
      _ = ∑ a, ∑ k, -((∑ d, P a d * DP d k j) * S a k) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro k _
        rw [hP k a j, hS a k, mul_neg]
      _ = -T := by simp only [Finset.sum_neg_distrib]; rfl
  rw [heq]
  linear_combination hneg / 2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

def holomorphicTwoFlux (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) (j d : ι) (x : E) : ℂ :=
  ∑ a, ∑ k, (ρ x * P x a d) * P x k j * S x a k

theorem holomorphicTwoFlux_derivative (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) {x : E}
    (hρ : DifferentiableAt ℝ ρ x)
    (hP : ∀ a k, DifferentiableAt ℝ (fun y => P y a k) x)
    (hS : ∀ a k, DifferentiableAt ℝ (fun y => S y a k) x) (v : ι → E) (j d : ι) :
    ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (holomorphicTwoFlux ρ P S j d) x (v d) =
      ∑ a, ∑ k, (ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a d) x (v d) *
        P x k j * S x a k + ρ x *
          (P x a d * ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y k j) x (v d) * S x a k +
            P x a d * P x k j * ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x (v d))) := by
  have h (a k : ι) : DifferentiableAt ℝ (fun y => (ρ y * P y a d) * P y k j * S y a k) x :=
    ((hρ.mul (hP a d)).mul (hP k j)).mul (hS a k)
  have hout := ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction.antiholomorphicDirectionalDerivative_sum
    (fun a y => ∑ k, (ρ y * P y a d) * P y k j * S y a k)
    (fun a => DifferentiableAt.fun_sum (fun k _ => h a k)) (v d)
  refine hout.trans (Finset.sum_congr rfl (fun a _ => ?_))
  have hin := ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction.antiholomorphicDirectionalDerivative_sum
    (fun k y => (ρ y * P y a d) * P y k j * S y a k) (h a) (v d)
  refine hin.trans (Finset.sum_congr rfl (fun k _ => ?_))
  have ht := ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction.antiholomorphicDirectionalDerivative_three
    (fun y => ρ y * P y a d) (fun y => P y k j) (fun y => S y a k)
    (hρ.mul (hP a d)) (hP k j) (hS a k) (v d)
  exact ht.trans (by ring)

theorem holomorphicTwoFlux_divergence_zero (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) {x : E}
    (hρ : DifferentiableAt ℝ ρ x)
    (hP : ∀ a k, DifferentiableAt ℝ (fun y => P y a k) x)
    (hS : ∀ a k, DifferentiableAt ℝ (fun y => S y a k) x) (v : ι → E)
    (hW : ∀ a, (∑ d, ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a d) x (v d)) = 0)
    (hT : ∀ a k j,
      (∑ d, P x a d * ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y k j) x (v d)) =
        ∑ d, P x k d * ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y a j) x (v d))
    (hskew : ∀ a k, S x k a = -S x a k)
    (hC : ∀ d a k, ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x (v d) = 0)
    (j : ι) :
    (∑ d, ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (holomorphicTwoFlux ρ P S j d) x (v d)) = 0 := by
  simp only [holomorphicTwoFlux_derivative ρ P S hρ hP hS v, hC, mul_zero, add_zero,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hw := ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction.weighted_two_flux_coefficient_zero (P x).transpose (S x)
    (fun d => Matrix.of fun a k =>
      ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a k) x (v d)) hW j
  have hm := skew_two_flux_metric_derivative_zero (P x) (S x)
    (fun d => Matrix.of fun a k =>
      ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y a k) x (v d)) hT hskew j
  change _ + ρ x * _ = 0
  exact (congrArg₂ (fun a b : ℂ => a + ρ x * b) hw hm).trans (by ring)

end

/-! The exact finite contraction turning the (2,0) metric pairing into its flux. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction

variable {ι : Type*} [Fintype ι]

theorem holomorphic_two_contraction (ρ : ℂ) (P S D : Matrix ι ι ℂ) :
    ρ * (2 * ∑ j, ∑ k, ∑ d, ∑ a, S a k * P a d * P k j * D d j) =
      2 * ∑ j, ∑ d, (∑ a, ∑ k, (ρ * P a d) * P k j * S a k) * D d j := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem holomorphic_two_raised_skew (ρ : ℂ) (P S : Matrix ι ι ℂ)
    (hS : ∀ a k, S k a = -S a k) (j d : ι) :
    (∑ a, ∑ k, (ρ * P a j) * P k d * S a k) =
      -(∑ a, ∑ k, (ρ * P a d) * P k j * S a k) := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  rw [hS]
  ring

theorem holomorphic_two_density_flux (ρ : ℂ) (P S D : Matrix ι ι ℂ)
    (hS : ∀ a k, S k a = -S a k) :
    ρ * (2 * ∑ j, ∑ k, ∑ d, ∑ a, S a k * P a d * P k j * (D d j - D j d)) =
      4 * ∑ j, ∑ d, (∑ a, ∑ k, (ρ * P a d) * P k j * S a k) * D d j := by
  let Q := fun j d => ∑ a, ∑ k, (ρ * P a d) * P k j * S a k
  have hQ (j d : ι) : Q d j = -Q j d := holomorphic_two_raised_skew ρ P S hS j d
  have hswap : (∑ j, ∑ d, Q j d * D j d) = -(∑ j, ∑ d, Q j d * D d j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro d _
    rw [hQ j d, neg_mul]
  have h := holomorphic_two_contraction ρ P S (Matrix.of fun d j => D d j - D j d)
  change _ = 2 * ∑ j, ∑ d, Q j d * (D d j - D j d) at h
  refine h.trans ?_
  change 2 * (∑ j, ∑ d, Q j d * (D d j - D j d)) = 4 * (∑ j, ∑ d, Q j d * D d j)
  simp only [mul_sub, Finset.sum_sub_distrib, hswap]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoDensity.Closedness
