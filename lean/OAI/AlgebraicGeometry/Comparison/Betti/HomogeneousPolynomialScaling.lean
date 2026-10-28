import OAI.AlgebraicGeometry.Comparison.Betti.MultilinearDiagonalPolynomial

/-! # Homogeneous Polynomial Scaling -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousPolynomialScaling.Dolbeault

noncomputable section

/-! Polynomial homogeneity gives the original scalar-rescaling identity on functions. -/

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem homogeneousPolynomial_eval_smul (P : MvPolynomial ι ℂ) (n : ℕ)
    (hP : P.IsHomogeneous n) (c : ℂ) (x : ι → ℂ) :
    MvPolynomial.eval (c • x) P = c ^ n * MvPolynomial.eval x P := by
  change MvPolynomial.eval₂ (RingHom.id ℂ) (c • x) P =
    c ^ n * MvPolynomial.eval₂ (RingHom.id ℂ) x P
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hn : e.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp he)
  have hsum : (∑ i : ι, e i) = n := (Finsupp.degree_eq_sum e).symm.trans hn
  simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousPolynomialScaling.Dolbeault
