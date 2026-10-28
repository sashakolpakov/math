import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ExtendedFibers
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination

/-! # Polynomial Products -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialProducts.Constructions.GenericPolynomial

noncomputable section

/-!
# Finite products of holomorphic polynomial families
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem differentiableOn_coeff_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Q : E → ℂ[X]} {U : Set E}
    (hP : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hQ : ∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) U) (j : ℕ) :
    DifferentiableOn ℂ (fun y => (P y * Q y).coeff j) U := by
  simp only [coeff_mul]
  exact DifferentiableOn.fun_sum (fun i _ => (hP i.1).fun_mul (hQ i.2))

theorem differentiableOn_coeff_prod
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : ι → E → ℂ[X]) {U : Set E}
    (hP : ∀ i j, DifferentiableOn ℂ (fun y => (P i y).coeff j) U)
    (s : Finset ι) : ∀ j, DifferentiableOn ℂ (fun y => (∏ i ∈ s, P i y).coeff j) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  | @insert i s hi ih =>
    intro j
    simp only [Finset.prod_insert hi]
    exact differentiableOn_coeff_mul (hP i) ih j

theorem not_eventually_zero_prod
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ι → E → ℂ) {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hn : ∀ i, ¬∀ᶠ y in 𝓝 x, f i y = 0) (s : Finset ι) :
    ¬∀ᶠ y in 𝓝 x, ∏ i ∈ s, f i y = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    intro hzero
    exact one_ne_zero hzero.self_of_nhds
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact GenericDegree.Constructions.GenericPolynomial.not_eventually_zero_mul hU hx (hf i)
      (AnalyticElimination.Constructions.Elimination.differentiableOn_finset_product s (fun j _ => hf j)) (hn i) ih

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialProducts.Constructions.GenericPolynomial
