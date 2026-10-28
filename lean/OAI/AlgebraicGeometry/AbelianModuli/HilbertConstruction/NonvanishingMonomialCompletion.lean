import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedExponentCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseNonvanishingBalancedMonomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomialExponentExtension

/-! # Nonvanishing Monomial Completion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion

noncomputable section

/-! Every nonvanishing determinant monomial at a sparse configuration
divides a nonvanishing balanced determinant monomial. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exponentMonomial_nsmul {κ : Type u} [Fintype κ] {R : Type v} [CommRing R]
    (D : κ → R) (a : κ → ℕ) (k : ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial D (k • a) = (Balanced.MonomialAlgebra.exponentMonomial D a) ^ k := by
  simp only [Balanced.MonomialAlgebra.exponentMonomial, Pi.smul_apply, nsmul_eq_mul, Nat.cast_id]
  simp_rw [Nat.mul_comm k, pow_mul]
  rw [Finset.prod_pow]

theorem exponentMonomial_ne_zero_iff {κ : Type u} [Fintype κ] {K : Type v} [Field K]
    (D : κ → K) (a : κ → ℕ) :
    Balanced.MonomialAlgebra.exponentMonomial D a ≠ 0 ↔ ∀ j, a j ≠ 0 → D j ≠ 0 := by
  constructor
  · intro h j hj hd
    have hp := Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
    exact hp (by rw [hd, zero_pow hj])
  · intro h
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    by_cases hj : a j = 0
    · rw [hj, pow_zero]
      exact one_ne_zero
    · exact pow_ne_zero _ (h j hj)

theorem sparseConfiguration_complete_nonvanishing_monomial
    {K : Type u} [Field K] {r m : ℕ}
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m)
    (b : (Fin r → Fin m) → ℕ)
    (hb : Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) b ≠ 0) :
    ∃ a c : (Fin r → Fin m) → ℕ,
      a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight ∧ c + b = a ∧
        Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a ≠ 0 := by
  obtain ⟨a, ha, hbal, hprod⟩ := SparseNonvanishingBalancedMonomial.sparseConfiguration_nonvanishing_balanced_determinant_monomial
    v hv hr hm hs
  let nz := fun τ : Fin r → Fin m => LabeledDeterminantPolynomials.labeledDeterminant τ v ≠ 0
  let A := MonomialExponentExtension.exponentExtendByZero nz a
  have hA : A ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight := by
    apply MonomialExponentExtension.exponentExtendByZero_balanced nz a DeterminantBlockDegrees.labeledDeterminantWeight
    convert hbal using 1 <;> congr!
  have hAb (τ) (hτ : b τ ≠ 0) : 0 < A τ := by
    have hnz : nz τ := (exponentMonomial_ne_zero_iff _ b).mp hb τ hτ
    simpa only [A, MonomialExponentExtension.exponentExtendByZero, dite_eq_left hnz] using ha ⟨τ, hnz⟩
  obtain ⟨k, _, c, hc, hka, _⟩ := SupportedExponentCompletion.supportedBalancedExponent_exists_completion
    DeterminantBlockDegrees.labeledDeterminantWeight A b hA hAb
  refine ⟨k • A, c, hka, hc, ?_⟩
  rw [exponentMonomial_nsmul]
  apply pow_ne_zero
  change Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (MonomialExponentExtension.exponentExtendByZero nz a) ≠ 0
  rw [MonomialExponentExtension.exponentMonomial_extendByZero]
  convert hprod using 1; congr!

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingMonomialCompletion
