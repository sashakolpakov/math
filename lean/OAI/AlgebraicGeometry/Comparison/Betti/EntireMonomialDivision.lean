import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters

/-! # Entire Monomial Division -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EntireMonomialDivision.Dolbeault

noncomputable section

section

/-! The actual contour division of an entire family by a coordinate
power has a holomorphic polynomial remainder of the required degree. -/

open _root_.Complex Set _root_.Metric _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters.Weierstrass OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def entireMonomialRemainder (G : P × ℂ → ℂ) (m : ℕ) (p : P) : Polynomial ℂ :=
  ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial m ((X : Polynomial ℂ) ^ m) (fun z => G (p, z)) 0 1

def entireMonomialLocalQuotient (G : P × ℂ → ℂ) (m : ℕ) (q : P × ℂ) : ℂ :=
  Holomorphic.DivisionFormula.Weierstrass.divisionQuotient ((X : Polynomial ℂ) ^ m) (fun z => G (q.1, z)) 0 1 q.2

theorem entireMonomial_local_division {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) (m : ℕ) :
    DifferentiableOn ℂ (entireMonomialLocalQuotient G m) (S ×ˢ ball (0 : ℂ) 1) ∧
      (∀ k, DifferentiableOn ℂ (fun p => (entireMonomialRemainder G m p).coeff k) S) ∧
      (∀ p ∈ S, ∀ k, m ≤ k → (entireMonomialRemainder G m p).coeff k = 0) ∧
      ∀ p ∈ S, ∀ z ∈ ball (0 : ℂ) 1, G (p, z) =
        (entireMonomialRemainder G m p).eval z + z ^ m * entireMonomialLocalQuotient G m (p, z) := by
  have hcoeff (k : ℕ) : DifferentiableOn ℂ
      (fun _ : P => (((X : Polynomial ℂ) ^ m).coeff k)) S := differentiableOn_const _
  have hdegree (p : P) (_hp : p ∈ S) : ((X : Polynomial ℂ) ^ m).natDegree = m := by simp
  have hn (p : P) (_hp : p ∈ S) (z : ℂ) (hz : z ∈ sphere 0 1) :
      ((X : Polynomial ℂ) ^ m).eval z ≠ 0 := by
    simp only [eval_pow, eval_X]
    apply pow_ne_zero
    have hnorm : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    exact norm_pos_iff.mp (hnorm.symm ▸ (by norm_num : 0 < (1 : ℝ)))
  have h := Holomorphic.DivisionParameters.Weierstrass.holomorphic_family_division (hS.prod isOpen_univ) hG hS hcoeff hdegree
    (by norm_num : 0 < (1 : ℝ)) (fun p hp => ⟨hp.1, mem_univ _⟩) hn
  unfold entireMonomialLocalQuotient entireMonomialRemainder
  simpa only [eval_pow, eval_X] using h

end

/-! Division of an entire holomorphic family by a coordinate power,
with a globally holomorphic quotient and the actual contour remainder. -/

open _root_.Complex Set _root_.Metric _root_.Polynomial Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters.Weierstrass OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def entireMonomialQuotient (G : P × ℂ → ℂ) (m : ℕ) (q : P × ℂ) : ℂ := by
  classical
  exact if q.2 = 0 then entireMonomialLocalQuotient G m q else
    (G q - (entireMonomialRemainder G m q.1).eval q.2) / q.2 ^ m

theorem entireMonomialQuotient_eq_local {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) (m : ℕ) {q : P × ℂ}
    (hq : q ∈ S ×ˢ ball (0 : ℂ) 1) :
    entireMonomialQuotient G m q = entireMonomialLocalQuotient G m q := by
  by_cases hz : q.2 = 0
  · simp only [entireMonomialQuotient, ite_eq_left hz]
  · rw [entireMonomialQuotient, ite_eq_right hz]
    apply (div_eq_iff (pow_ne_zero m hz)).mpr
    have h := (entireMonomial_local_division hS hG m).2.2.2 q.1 hq.1 q.2 hq.2
    linear_combination h

theorem entireMonomialRemainder_eval_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) (m : ℕ) :
    DifferentiableOn ℂ (fun q : P × ℂ => (entireMonomialRemainder G m q.1).eval q.2) (S ×ˢ univ) := by
  have h := entireMonomial_local_division hS hG m
  apply ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_polynomial_eval h.2.1
  intro p hp
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact h.2.2.1 p hp k hk.le

theorem entireMonomialQuotient_holomorphic {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) (m : ℕ) :
    DifferentiableOn ℂ (entireMonomialQuotient G m) (S ×ˢ univ) := by
  intro q hq
  by_cases hz : q.2 = 0
  · have hmem : q ∈ S ×ˢ ball (0 : ℂ) 1 := ⟨hq.1, by simp [hz]⟩
    have hd := (entireMonomial_local_division hS hG m).1.differentiableAt
      ((hS.prod isOpen_ball).mem_nhds hmem)
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(hS.prod isOpen_ball).mem_nhds hmem] with p hp
    exact entireMonomialQuotient_eq_local hS hG m hp
  · have hg := hG.differentiableAt ((hS.prod isOpen_univ).mem_nhds hq)
    have hr := (entireMonomialRemainder_eval_holomorphic hS hG m).differentiableAt
      ((hS.prod isOpen_univ).mem_nhds hq)
    have hi : DifferentiableAt ℂ (fun p : P × ℂ => (p.2 ^ m)⁻¹) q :=
      (differentiableAt_snd.pow m).fun_inv (pow_ne_zero m hz)
    have hd : DifferentiableAt ℂ (fun p : P × ℂ =>
        (G p - (entireMonomialRemainder G m p.1).eval p.2) * (p.2 ^ m)⁻¹) q :=
      (hg.sub hr).fun_mul hi
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hz] with p hp
    simp only [entireMonomialQuotient, ite_eq_right hp, div_eq_mul_inv]

theorem entireMonomialDivision_identity {G : P × ℂ → ℂ} {S : Set P} (hS : IsOpen S)
    (hG : DifferentiableOn ℂ G (S ×ˢ univ)) (m : ℕ) {p : P} (hp : p ∈ S) (z : ℂ) :
    G (p, z) = (entireMonomialRemainder G m p).eval z + z ^ m * entireMonomialQuotient G m (p, z) := by
  by_cases hz : z = 0
  · subst z
    have hmem : (p, (0 : ℂ)) ∈ S ×ˢ ball (0 : ℂ) 1 := ⟨hp, by simp⟩
    rw [entireMonomialQuotient_eq_local hS hG m hmem]
    exact (entireMonomial_local_division hS hG m).2.2.2 p hp 0 (by simp)
  · rw [entireMonomialQuotient, ite_eq_right hz]
    field_simp
    ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.EntireMonomialDivision.Dolbeault
