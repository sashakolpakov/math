import Mathlib

/-! # Polynomial Functional Extension -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialFunctionalExtension.Construction

noncomputable section

/-! A linear functional on polynomial coordinates extends coefficientwise
to any coefficient algebra, and commutes with specialization. -/

open scoped Classical
open _root_.MvPolynomial

def polynomialFunctionalMap {k K σ : Type*} [Field k] [CommRing K]
    (ι : k →+* K) (φ : MvPolynomial σ k →ₗ[k] k) : MvPolynomial σ K →ₗ[K] K :=
  (MvPolynomial.basisMonomials σ K).constr K (fun m => ι (φ (monomial m 1)))

theorem polynomialFunctionalMap_monomial {k K σ : Type*} [Field k] [CommRing K]
    (ι : k →+* K) (φ : MvPolynomial σ k →ₗ[k] k) (m : σ →₀ ℕ) (c : K) :
    polynomialFunctionalMap ι φ (monomial m c) = c * ι (φ (monomial m 1)) := by
  have he : (monomial m c : MvPolynomial σ K) = c • (MvPolynomial.basisMonomials σ K) m := by
    change monomial m c = c • monomial m 1
    rw [smul_monomial, smul_eq_mul, mul_one]
  unfold polynomialFunctionalMap
  rw [he, map_smul, Module.Basis.constr_basis, smul_eq_mul]

theorem polynomialFunctionalMap_coefficient_map
    {k K σ : Type*} [Field k] [CommRing K]
    (ι : k →+* K) (φ : MvPolynomial σ k →ₗ[k] k) (p : MvPolynomial σ k) :
    polynomialFunctionalMap ι φ (MvPolynomial.map ι p) = ι (φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
      rw [MvPolynomial.map_monomial, polynomialFunctionalMap_monomial]
      have hm : φ (monomial m c) = c * φ (monomial m 1) := by
        have he : (monomial m c : MvPolynomial σ k) = c • monomial m 1 := by
          rw [smul_monomial, smul_eq_mul, mul_one]
        rw [he, map_smul, smul_eq_mul]
      rw [hm, map_mul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem polynomialFunctionalMap_specialize
    {k A B σ : Type*} [Field k] [CommRing A] [CommRing B]
    (ι : k →+* A) (f : A →+* B) (φ : MvPolynomial σ k →ₗ[k] k) (p : MvPolynomial σ A) :
    f (polynomialFunctionalMap ι φ p) =
      polynomialFunctionalMap (f.comp ι) φ (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
      rw [MvPolynomial.map_monomial, polynomialFunctionalMap_monomial,
        polynomialFunctionalMap_monomial, map_mul]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialFunctionalExtension.Construction
