import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionFormula
import OAI.AlgebraicGeometry.Comparison.Betti.ParametricCauchyIntegral

/-! # Division Parameters -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters.Weierstrass

noncomputable section

section

/-! Exact polynomial division of a holomorphic family has a jointly
holomorphic quotient and holomorphic, strictly bounded remainder coefficients. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem differentiableOn_divisionQuotient
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {U : Set E} (hU : IsOpen U) {P : E → Polynomial ℂ} {d : ℕ}
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0) :
    DifferentiableOn ℂ (fun p : E × ℂ => DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2)
      (U ×ˢ ball c R) := by
  have hEval := ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_polynomial_eval hcoeff hdegree
  let V : Set (E × ℂ) := W ∩ ((U ×ˢ univ) ∩
    (fun p : E × ℂ => (P p.1).eval p.2) ⁻¹' ({0} : Set ℂ)ᶜ)
  have hV : IsOpen V := hW.inter (hEval.continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) isClosed_singleton.isOpen_compl)
  let G : E × ℂ → ℂ := fun p => F p / (P p.1).eval p.2
  have hVU : V ⊆ U ×ˢ univ := fun _ hp => hp.2.1
  have hG : DifferentiableOn ℂ G V :=
    by simpa only [G, div_eq_mul_inv] using
      (hF.mono inter_subset_left).fun_mul ((hEval.mono hVU).fun_inv (fun _ hp => hp.2.2))
  have hUV : U ×ˢ sphere c R ⊆ V := fun p hp =>
    ⟨hUW hp, ⟨hp.1, mem_univ _⟩, hn p.1 hp.1 p.2 hp.2⟩
  have h := ParametricCauchyIntegral.Weierstrass.differentiableOn_parametricCauchyIntegral hV hG hU hR hUV
  have he : (fun p : E × ℂ => DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2) =
      ParametricCauchyIntegral.Weierstrass.parametricCauchyIntegral G c R := by
    funext p
    simp only [DivisionFormula.Weierstrass.divisionQuotient, ParametricCauchyIntegral.Weierstrass.parametricCauchyIntegral, G, div_div]
  rw [he]
  exact h

theorem holomorphic_family_division
    {F : E × ℂ → ℂ} {W : Set (E × ℂ)} (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {U : Set E} (hU : IsOpen U) {P : E → Polynomial ℂ} {d : ℕ}
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree = d)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hUW : U ×ˢ closedBall c R ⊆ W)
    (hn : ∀ y ∈ U, ∀ z ∈ sphere c R, (P y).eval z ≠ 0) :
    DifferentiableOn ℂ (fun p : E × ℂ => DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2)
        (U ×ˢ ball c R) ∧
      (∀ k : ℕ, DifferentiableOn ℂ
        (fun y => (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial d (P y) (fun z => F (y, z)) c R).coeff k) U) ∧
      (∀ y ∈ U, ∀ k : ℕ, d ≤ k →
        (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial d (P y) (fun z => F (y, z)) c R).coeff k = 0) ∧
      ∀ y ∈ U, ∀ w ∈ ball c R, F (y, w) =
        (ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial d (P y) (fun z => F (y, z)) c R).eval w +
          (P y).eval w * DivisionFormula.Weierstrass.divisionQuotient (P y) (fun z => F (y, z)) c R w := by
  have hbd : U ×ˢ sphere c R ⊆ W := fun p hp => hUW ⟨hp.1, sphere_subset_closedBall hp.2⟩
  refine ⟨differentiableOn_divisionQuotient hW hF hU hcoeff
    (fun y hy => (hdegree y hy).le) hR.le hbd hn,
    ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_remainderPolynomial_coeff hW hF hU hcoeff
      (fun y hy => (hdegree y hy).le) hR.le hbd hn, ?_, ?_⟩
  · intro y hy k hk
    simpa only [hdegree y hy] using DivisionFormula.Weierstrass.remainderPolynomial_coeff_zero (P y) (fun z => F (y, z)) c R k
      (by rw [hdegree y hy]; exact hk)
  · intro y hy w hw
    have hFy : DifferentiableOn ℂ (fun z => F (y, z)) (closedBall c R) :=
      hF.comp ((differentiable_const y).prodMk differentiable_id).differentiableOn
        (fun z hz => hUW ⟨hy, hz⟩)
    simpa only [hdegree y hy] using DivisionFormula.Weierstrass.holomorphic_division_formula (P y) (fun z => F (y, z)) c R w hR hFy (hn y hy) hw

end

/-! A distinguished polynomial family has no zeros on any sufficiently
localized family of circles of positive radius around its center. -/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem polynomial_circle_neighborhood {P : E → ℂ[X]} {d : ℕ} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hd : ∀ y ∈ U, (P y).natDegree ≤ d) {c : ℂ}
    (hcenter : P x = (X - C c) ^ d) {R : ℝ} (hR : 0 < R) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, ∀ z ∈ sphere c R, (P y).eval z ≠ 0 := by
  have hEval := ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_polynomial_eval hcoeff hd
  let Z := (U ×ˢ (univ : Set ℂ)) ∩
    (fun p : E × ℂ => (P p.1).eval p.2) ⁻¹' ({0} : Set ℂ)ᶜ
  have hZ : IsOpen Z := hEval.continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) isClosed_singleton.isOpen_compl
  have hbase : ({x} : Set E) ×ˢ sphere c R ⊆ Z := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    rcases mem_singleton_iff.mp hy with rfl
    refine ⟨⟨hx, mem_univ z⟩, ?_⟩
    change (P y).eval z ≠ 0
    rw [hcenter, eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero d (sub_ne_zero.mpr (ne_of_mem_sphere hz hR.ne'))
  obtain ⟨V, T, hV, _, hxV, hT, hVT⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere c R) hZ hbase
  exact ⟨U ∩ V, hU.inter hV, ⟨hx, hxV (mem_singleton x)⟩, inter_subset_left,
    fun y hy z hz => (hVT (show (y, z) ∈ V ×ˢ T from ⟨hy.2, hT hz⟩)).2⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters.Weierstrass
