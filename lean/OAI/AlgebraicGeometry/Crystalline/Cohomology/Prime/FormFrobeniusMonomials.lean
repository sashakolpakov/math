import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusWeights
import Mathlib.Algebra.MvPolynomial.Expand

/-! # Form Frobenius Monomials -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusMonomials.PrimeFormFrobeniusMonomials

noncomputable section

/-! # Polynomial coefficients of the actual power-substitution pullback -/

open Classical

universe u

variable (p : ℕ) [Fact p.Prime] (σ : Type u) [Fintype σ] [LinearOrder σ]

omit [Fact p.Prime] [Fintype σ] in
theorem exteriorExponent_apply (n : ℕ) (s : Set.powersetCard σ n) (i : σ) :
    (∑ j : Fin n, Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) (p - 1)) i =
      if i ∈ s then p - 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    obtain ⟨j, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
    simp only [Finsupp.single_apply, (Set.powersetCard.ofFinEmbEquiv.symm s).injective.eq_iff,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.single_eq_of_ne
    intro he
    exact hi ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mp ⟨j, he.symm⟩)

theorem raiseExponent_eq (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d =
      p • d + ∑ j : Fin n, Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) (p - 1) := by
  ext i
  change PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raiseIndex p
    (FormFrobeniusWeights.PrimeFormFrobeniusWeights.indicator σ s i) (d i) = _
  rw [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, exteriorExponent_apply]
  unfold PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raiseIndex FormFrobeniusWeights.PrimeFormFrobeniusWeights.indicator
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi, Nat.mul_add, Nat.mul_one]
    exact Nat.add_sub_assoc (Nat.Prime.pos (Fact.out : p.Prime)) (p * d i)
  · simp [hi]

variable (R : Type u) [CommRing R]

theorem pullback_coefficient (n : ℕ) (d : σ →₀ ℕ) (s : Set.powersetCard σ n) :
    MvPolynomial.expand p (MvPolynomial.monomial d (1 : R)) *
        (∏ j : Fin n, (p : MvPolynomial σ R) *
          MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j) ^ (p - 1)) =
      MvPolynomial.monomial (FormFrobeniusWeights.PrimeFormFrobeniusWeights.raiseExponent p σ s d) ((p : R) ^ n) := by
  let e : σ →₀ ℕ := ∑ j : Fin n,
    Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) (p - 1)
  have hprod : (∏ j : Fin n,
      (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j) : MvPolynomial σ R) ^ (p - 1)) =
        MvPolynomial.monomial e 1 := by
    simp only [MvPolynomial.X_pow_eq_monomial]
    exact (MvPolynomial.monomial_sum_one Finset.univ _).symm
  rw [MvPolynomial.expand_monomial, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, hprod]
  rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial σ R) p, ← map_pow,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial, mul_one, one_mul]
  rw [raiseExponent_eq]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.FormFrobeniusMonomials.PrimeFormFrobeniusMonomials
