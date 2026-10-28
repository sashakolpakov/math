import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedHomogeneousPolynomials
import Mathlib.Algebra.MvPolynomial.Division

/-! # Normalized Polynomial Supports -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialSupports.Dolbeault

noncomputable section

section

/-! The coordinate remainder retains exactly the monomials with zero exponent in that coordinate. -/

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialCoordinateRemainder_support (P : MvPolynomial ι ℂ) (i : ι)
    (e : ι →₀ ℕ) (he : e ∈ (MvPolynomial.modMonomial P (Finsupp.single i 1)).support) : e i = 0 := by
  have h := MvPolynomial.mem_support_iff.mp he
  by_contra hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  exact h (MvPolynomial.coeff_modMonomial_of_le P hle)

omit [Fintype ι] [DecidableEq ι] in
theorem polynomialCoordinateRemainder_homogeneous (P : MvPolynomial ι ℂ) (k : ℕ)
    (hP : P.IsHomogeneous k) (i : ι) :
    (MvPolynomial.modMonomial P (Finsupp.single i 1)).IsHomogeneous k := by
  intro e he
  have hei := polynomialCoordinateRemainder_support P i e (MvPolynomial.mem_support_iff.mpr he)
  have hnle : ¬Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff, hei]
    decide
  exact hP (fun hz => he ((MvPolynomial.coeff_modMonomial_of_not_le P hnle).trans hz))

theorem polynomialCoordinateRemainder_eval_update (P : MvPolynomial ι ℂ) (i : ι) (x : ι → ℂ) :
    MvPolynomial.eval (Function.update x i 0) (MvPolynomial.modMonomial P (Finsupp.single i 1)) =
      MvPolynomial.eval x (MvPolynomial.modMonomial P (Finsupp.single i 1)) := by
  let R := MvPolynomial.modMonomial P (Finsupp.single i 1)
  change MvPolynomial.eval₂ (RingHom.id ℂ) (Function.update x i 0) R =
    MvPolynomial.eval₂ (RingHom.id ℂ) x R
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro e he
  apply congrArg (fun z : ℂ => (RingHom.id ℂ) (AddMonoidAlgebra.coeff (R) (e)) * z)
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    rw [polynomialCoordinateRemainder_support P i e he, pow_zero, pow_zero]
  · rw [Function.update_of_ne hj]

theorem polynomialCoordinateRemainder_eval (P : MvPolynomial ι ℂ) (i : ι) (x : ι → ℂ) :
    MvPolynomial.eval x (MvPolynomial.modMonomial P (Finsupp.single i 1)) =
      MvPolynomial.eval (Function.update x i 0) P := by
  have h := congrArg (MvPolynomial.eval (Function.update x i 0))
    (MvPolynomial.divMonomial_add_modMonomial_single P i)
  rw [map_add, map_mul, MvPolynomial.eval_X, Function.update_self, zero_mul, zero_add] at h
  exact (polynomialCoordinateRemainder_eval_update P i x).symm.trans h

end

/-! Coordinate-hyperplane vanishing is exactly positivity of the corresponding monomial exponents. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polynomialCoordinateRemainder_zero_of_vanishing (P : MvPolynomial ι ℂ) (k : ℕ)
    (hP : P.IsHomogeneous k) (i : ι)
    (hi : ∀ x : ι → ℂ, x i = 0 → MvPolynomial.eval x P = 0) :
    MvPolynomial.modMonomial P (Finsupp.single i 1) = 0 :=
  (polynomialCoordinateRemainder_homogeneous P k hP i).eq_zero_of_forall_eval_eq_zero
    (fun x => (polynomialCoordinateRemainder_eval P i x).trans
      (hi (Function.update x i 0) (Function.update_self i 0 x)))

theorem normalizedHomogeneousPolynomial_support_positive (J : Finset ι) (k : ℕ)
    (P : NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials J k) (e : ι →₀ ℕ) (he : e ∈ P.val.support)
    (i : ι) (hi : i ∈ J) : 0 < e i := by
  by_contra h
  have hei : e i = 0 := by omega
  have hnle : ¬Finsupp.single i 1 ≤ e := by
    rw [Finsupp.single_le_iff, hei]
    decide
  have hzero := polynomialCoordinateRemainder_zero_of_vanishing P.val k P.property.1 i (P.property.2 i hi)
  have hc := MvPolynomial.coeff_modMonomial_of_not_le P.val hnle
  rw [hzero, AddMonoidAlgebra.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp he) hc.symm

omit [Fintype ι] [DecidableEq ι] in
theorem homogeneousPolynomial_normalized_of_support (J : Finset ι) (k : ℕ)
    (P : MvPolynomial ι ℂ) (hP : P.IsHomogeneous k)
    (hs : ∀ e ∈ P.support, ∀ i ∈ J, 0 < e i) :
    P ∈ NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials J k := by
  refine ⟨hP, ?_⟩
  intro i hi x hx
  apply MvPolynomial.eval₂Hom_eq_zero
  intro e he
  exact ⟨i, Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (hs e (MvPolynomial.mem_support_iff.mpr he) i hi)), hx⟩

theorem normalizedHomogeneousPolynomials_mem_iff (J : Finset ι) (k : ℕ) (P : MvPolynomial ι ℂ) :
    P ∈ NormalizedHomogeneousPolynomials.Dolbeault.normalizedHomogeneousPolynomials J k ↔
      P.IsHomogeneous k ∧ ∀ e ∈ P.support, ∀ i ∈ J, 0 < e i := by
  constructor
  · intro h
    exact ⟨h.1, normalizedHomogeneousPolynomial_support_positive J k ⟨P, h⟩⟩
  · rintro ⟨hP, hs⟩
    exact homogeneousPolynomial_normalized_of_support J k P hP hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialSupports.Dolbeault
