import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms

/-! # Germ Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialCoefficients.AnalyticLocal

noncomputable section

/-! Coefficients, evaluation, and monicity of polynomials formed from the
actual holomorphic germs of a polynomial family. -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (x : E) (P : E → ℂ[X]) (d : ℕ) {U : Set E} (hU : IsOpen U) (hx : x ∈ U)
  (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)

theorem polynomialOfFamily_coeff (k : ℕ) :
    (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff).coeff k =
      if k ≤ d then ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x (fun y => (P y).coeff k) hU hx (hcoeff k) else 0 := by
  simp [ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']

theorem polynomialOfFamily_map_value (hd : (P x).natDegree ≤ d) :
    (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff).map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) = P x := by
  ext k
  rw [coeff_map, polynomialOfFamily_coeff]
  split_ifs with hk
  · rfl
  · rw [map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (hd.trans_lt (lt_of_not_ge hk))).symm

theorem polynomialOfFamily_monic_degree
    (hP : ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d) :
    (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff).Monic ∧
      (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff).natDegree = d := by
  let Q := ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff
  have htop : Q.coeff d = 1 := by
    rw [polynomialOfFamily_coeff, ite_eq_left le_rfl]
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hP y hy).2 ▸ (hP y hy).1.coeff_natDegree
  have hle : Q.natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [polynomialOfFamily_coeff, ite_eq_right (not_le_of_gt hk)]
  have hdeg : Q.natDegree = d := le_antisymm hle
    (le_natDegree_of_ne_zero (by rw [htop]; exact one_ne_zero))
  refine ⟨?_, hdeg⟩
  change Q.coeff Q.natDegree = 1
  rw [hdeg, htop]

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialCoefficients.AnalyticLocal
