import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Polynomial Substitution Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSubstitutionDegree.Dimension

/-! Substituting polynomials of bounded degree changes total degree by at most a fixed factor. -/

open _root_.MvPolynomial

theorem totalDegree_aeval_monomial_le
    {K σ τ : Type*} [CommSemiring K] (q : σ → MvPolynomial τ K)
    (c : ℕ) (hq : ∀ i, (q i).totalDegree ≤ c) (s : σ →₀ ℕ) (a : K) :
    (MvPolynomial.aeval q (MvPolynomial.monomial s a)).totalDegree ≤
      (s.sum fun _ e => e) * c := by
  classical
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  change (MvPolynomial.C a : MvPolynomial τ K).totalDegree +
    (s.prod fun i k => q i ^ k).totalDegree ≤ _
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd s.support (fun i => q i ^ s i)).trans
  calc
    ∑ i ∈ s.support, (q i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i * c :=
      Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_pow (q i) (s i)).trans
        (Nat.mul_le_mul_left (s i) (hq i)))
    _ = (s.sum fun _ e => e) * c := by rw [Finsupp.sum, Finset.sum_mul]

theorem totalDegree_aeval_le
    {K σ τ : Type*} [CommSemiring K] (q : σ → MvPolynomial τ K)
    (c : ℕ) (hq : ∀ i, (q i).totalDegree ≤ c) (p : MvPolynomial σ K) :
    (MvPolynomial.aeval q p).totalDegree ≤ p.totalDegree * c := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  exact (totalDegree_aeval_monomial_le q c hq s (p.coeff s)).trans
    (Nat.mul_le_mul_right c (MvPolynomial.le_totalDegree hs))

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSubstitutionDegree.Dimension
