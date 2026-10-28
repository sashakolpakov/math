import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveRealDeterminantBalance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedNaturalExponents

/-! # Sparse Nonvanishing Balanced Monomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseNonvanishingBalancedMonomial

noncomputable section

/-! A sparse projective configuration admits a nonvanishing balanced
determinant monomial, with positive exponents on every nonzero determinant. -/
open scoped BigOperators Classical
universe u

theorem sparseConfiguration_nonvanishing_balanced_determinant_monomial
    {K : Type u} [Field K] {r m : ℕ}
    (v : Fin m → Fin r → K) (hv : ∀ i, v i ≠ 0) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hs : ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
      r * (Finset.univ.filter (fun i => v i ∈ W)).card < m) :
    ∃ a : CenteredDeterminantWeights.nonzeroDeterminantLabels v → ℕ, (∀ σ, 0 < a σ) ∧
      a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid (fun σ i => DeterminantBlockDegrees.labeledDeterminantWeight σ.val i) ∧
      Balanced.MonomialAlgebra.exponentMonomial (fun σ : CenteredDeterminantWeights.nonzeroDeterminantLabels v => LabeledDeterminantPolynomials.labeledDeterminant σ.val v) a ≠ 0 := by
  obtain ⟨c, hc, hbal⟩ := PositiveRealDeterminantBalance.sparseConfiguration_positive_real_balanced_determinants v hv hr hm hs
  obtain ⟨a, ha, habal⟩ := Positive.BalancedNaturalExponents.exists_positive_balanced_natural_exponent
    (fun σ : CenteredDeterminantWeights.nonzeroDeterminantLabels v => DeterminantBlockDegrees.labeledDeterminantWeight σ.val) c hc hbal
  refine ⟨a, ha, habal, ?_⟩
  apply Finset.prod_ne_zero_iff.mpr
  intro σ _
  exact pow_ne_zero _ σ.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseNonvanishingBalancedMonomial
