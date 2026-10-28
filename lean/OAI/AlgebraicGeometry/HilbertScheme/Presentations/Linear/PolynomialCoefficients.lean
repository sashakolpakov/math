import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.Ideal.Maps

/-! # Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialCoefficients.GradedHilbert

noncomputable section

/-! Linear coefficients extract module generators from polynomial relations. -/

open _root_.MvPolynomial

variable {R ι : Type*} [CommRing R]

def polynomialLinearPart : MvPolynomial ι R →ₗ[R] (ι → R) where
  toFun p i := AddMonoidAlgebra.coeff (p) ((Finsupp.single i 1))
  map_add' p q := by ext i; rfl
  map_smul' r p := funext (fun i => coeff_smul (Finsupp.single i 1) r p)

theorem polynomialLinearPart_eq_derivative (p : MvPolynomial ι R) (i : ι) :
    polynomialLinearPart p i = constantCoeff (pderiv i p) := by
  simp [polynomialLinearPart, constantCoeff_eq, coeff_pderiv]

theorem polynomialLinearPart_mul (p q : MvPolynomial ι R) :
    polynomialLinearPart (p * q) = constantCoeff q • polynomialLinearPart p +
      constantCoeff p • polynomialLinearPart q := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, polynomialLinearPart_eq_derivative,
    pderiv_mul, map_add, map_mul]
  rw [mul_comm (constantCoeff (pderiv i p))]

theorem polynomialLinearPart_C (r : R) : polynomialLinearPart (C r : MvPolynomial ι R) = 0 := by
  funext i
  rw [polynomialLinearPart_eq_derivative, pderiv_C, map_zero]
  rfl

theorem polynomialLinearPart_X [DecidableEq ι] (j : ι) :
    polynomialLinearPart (X j : MvPolynomial ι R) = Pi.single j 1 := by
  funext i
  rw [polynomialLinearPart_eq_derivative]
  by_cases hij : i = j
  · subst j
    simp
  · simp [pderiv_X_of_ne (Ne.symm hij), hij]

def linearVariableSubstitution (g : ι → R) : MvPolynomial ι R →ₐ[R] Polynomial R :=
  aeval (fun i => Polynomial.C (g i) * Polynomial.X)

theorem linearVariableSubstitution_coeff_zero (g : ι → R) (p : MvPolynomial ι R) :
    (linearVariableSubstitution g p).coeff 0 = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [linearVariableSubstitution]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p i hp => simp [linearVariableSubstitution, Polynomial.mul_coeff_zero]

theorem linearVariableSubstitution_coeff_one [Fintype ι]
    (g : ι → R) (p : MvPolynomial ι R) :
    (linearVariableSubstitution g p).coeff 1 = ∑ i, polynomialLinearPart p i * g i := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [linearVariableSubstitution, polynomialLinearPart_C]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, polynomialLinearPart_mul]
    have hx : linearVariableSubstitution g (X j) = Polynomial.C (g j) * Polynomial.X := by
      simp [linearVariableSubstitution]
    rw [hx, Polynomial.mul_coeff_one, linearVariableSubstitution_coeff_zero]
    simp [polynomialLinearPart_X, Pi.single_apply]

theorem polynomialLinearPart_mem_span
    (B : Set (MvPolynomial ι R)) (hB : ∀ b ∈ B, constantCoeff b = 0)
    {p : MvPolynomial ι R} (hp : p ∈ Ideal.span B) :
    constantCoeff p = 0 ∧ polynomialLinearPart p ∈ Submodule.span R (polynomialLinearPart '' B) := by
  induction hp using Submodule.span_induction with
  | mem b hb => exact ⟨hB b hb, Submodule.subset_span ⟨b, hb, rfl⟩⟩
  | zero => exact ⟨map_zero _, by simp only [map_zero]; exact Submodule.zero_mem _⟩
  | add p q _ _ hp hq =>
    exact ⟨by rw [map_add, hp.1, hq.1, add_zero], by
      rw [map_add]
      exact Submodule.add_mem _ hp.2 hq.2⟩
  | smul a b _ hb =>
    change constantCoeff (a * b) = 0 ∧ polynomialLinearPart (a * b) ∈ _
    refine ⟨by rw [map_mul, hb.1, mul_zero], ?_⟩
    rw [polynomialLinearPart_mul, hb.1, zero_smul, zero_add]
    exact Submodule.smul_mem _ (constantCoeff a) hb.2

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialCoefficients.GradedHilbert
