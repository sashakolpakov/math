import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.MonomialEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight

/-! # Homogeneous Laurent Monomial Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurentMonomialEvaluation.Dolbeault

noncomputable section

/-! The affine Laurent monomial with its frame factor is the original homogeneous Laurent monomial. -/

open scoped BigOperators

theorem finset_zpow_sum_nonzero {ι : Type} (s : Finset ι) (c : ℂ) (hc : c ≠ 0) (e : ι → ℤ) :
    c ^ (∑ i ∈ s, e i) = ∏ i ∈ s, c ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hc, ih]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem homogeneousLaurentMonomial_chart (e : ι →₀ ℤ) (i : ι) (x : ι → ℂ) (hi : x i ≠ 0) :
    x i ^ e.degree * (∏ j : {j : ι // j ≠ i}, (x j.val / x i) ^ e j.val) =
      ∏ j, x j ^ e j := by
  have hs : (∑ j : {j : ι // j ≠ i}, e j.val) + e i = e.degree := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp) (fun j => e j)]
    exact (Finset.sum_erase_add Finset.univ (fun j => e j) (Finset.mem_univ i)).trans
      (Finsupp.degree_eq_sum e).symm
  have hp : (∏ j : {j : ι // j ≠ i}, x j.val ^ e j.val) * x i ^ e i = ∏ j, x j ^ e j := by
    rw [← Finset.prod_subtype (Finset.univ.erase i) (by simp) (fun j => x j ^ e j)]
    exact Finset.prod_erase_mul Finset.univ (fun j => x j ^ e j) (Finset.mem_univ i)
  have hr : (∏ j : {j : ι // j ≠ i}, (x j.val / x i) ^ e j.val) =
      (∏ j : {j : ι // j ≠ i}, x j.val ^ e j.val) /
        x i ^ (∑ j : {j : ι // j ≠ i}, e j.val) := by
    simp_rw [div_zpow]
    rw [Finset.prod_div_distrib, ← finset_zpow_sum_nonzero Finset.univ (x i) hi]
  rw [hr, ← hs, zpow_add₀ hi]
  calc
    (x i ^ (∑ j : {j : ι // j ≠ i}, e j.val) * x i ^ e i) *
        ((∏ j : {j : ι // j ≠ i}, x j.val ^ e j.val) /
          x i ^ (∑ j : {j : ι // j ≠ i}, e j.val)) =
        (∏ j : {j : ι // j ≠ i}, x j.val ^ e j.val) * x i ^ e i := by
      field_simp
    _ = _ := hp

theorem coordinateLaurentMonomial_homogeneous {q : ℕ} (a : Fin (q + 1) → ι) (d : ℤ)
    (e : SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a))
    (x : ι → ℂ) (hx : x (a 0) ≠ 0) :
    x (a 0) ^ d * (∏ j : {j : ι // j ≠ a 0}, (x j.val / x (a 0)) ^ e.val j) =
      ∏ j, x j ^ (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e).val.val j := by
  have h := homogeneousLaurentMonomial_chart
    (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e).val.val (a 0) x hx
  rw [(SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e).val.property] at h
  have hp : (∏ j : {j : ι // j ≠ a 0},
      (x j.val / x (a 0)) ^ (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d e).val.val j.val) =
      ∏ j : {j : ι // j ≠ a 0}, (x j.val / x (a 0)) ^ e.val j := by
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg (fun z : ℤ => (x j.val / x (a 0)) ^ z)
      (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne a d e j.val j.property)
  exact (congrArg (x (a 0) ^ d * ·) hp).symm.trans h

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousLaurentMonomialEvaluation.Dolbeault
