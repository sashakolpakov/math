import OAI.AlgebraicGeometry.Comparison.Betti.MonicGermRepresentative
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe
import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.Division
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DivisionParameters

/-! # Germ Polynomial Division -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialDivision.AnalyticLocal

noncomputable section

/-! Division by a distinguished monic polynomial in the actual local
ring has a polynomial remainder with strictly smaller degree. -/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem germ_polynomial_division (x : E) (c : ℂ) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (hQ : Q.Monic)
    (hcenter : Q.map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) = (X - C c) ^ Q.natDegree) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) :
    ∃ (b : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) (S : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]),
      (∀ k : ℕ, Q.natDegree ≤ k → S.coeff k = 0) ∧
      a = GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c S + GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c Q * b := by
  obtain ⟨F, hFa, W, hW, hxc, hF⟩ := a.property
  obtain ⟨P, U₀, hU₀, hx₀, hc₀, hP₀, hv, hQrepr⟩ := MonicGermRepresentative.AnalyticLocal.exists_monic_germ_representative x Q hQ
  obtain ⟨R, U₁, hR, hU₁, hx₁, hUW₁⟩ := Coordinate.Division.Weierstrass.exists_product_closedDisk hW hxc
  obtain ⟨U₂, hU₂, hx₂, hsub₂, hPn⟩ := Holomorphic.DivisionParameters.Weierstrass.polynomial_circle_neighborhood hU₀ hx₀ hc₀
    (fun y hy => (hP₀ y hy).2.le) (hv.trans hcenter) hR
  let U := U₁ ∩ U₂
  have hU : IsOpen U := hU₁.inter hU₂
  have hx : x ∈ U := ⟨hx₁, hx₂⟩
  have hsub : U ⊆ U₀ := fun y hy => hsub₂ hy.2
  have hc : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U :=
    fun k => (hc₀ k).mono hsub
  have hd : ∀ y ∈ U, (P y).natDegree = Q.natDegree := fun y hy => (hP₀ y (hsub hy)).2
  have hUW : U ×ˢ closedBall c R ⊆ W := fun p hp => hUW₁ ⟨hp.1.1, hp.2⟩
  obtain ⟨hq, hrem, hremzero, hdivision⟩ := Holomorphic.DivisionParameters.Weierstrass.holomorphic_family_division hW hF hU hc hd hR
    hUW (fun y hy => hPn y hy.2)
  let A : E → ℂ[X] := fun y => ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt.Constructions.ContourRemainder.remainderPolynomial Q.natDegree (P y) (fun z => F (y, z)) c R
  let S := ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x A Q.natDegree hU hx hrem
  have hSdeg : ∀ y ∈ U, (A y).natDegree ≤ Q.natDegree := by
    intro y hy
    exact natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => hremzero y hy k hk.le)
  let q : E × ℂ → ℂ := fun p =>
    Holomorphic.DivisionFormula.Weierstrass.divisionQuotient (P p.1) (fun z => F (p.1, z)) c R p.2
  have hxcU : (x, c) ∈ U ×ˢ ball c R := ⟨hx, mem_ball_self hR⟩
  let b := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (x, c) q (hU.prod isOpen_ball) hxcU hq
  have hQnew : ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P Q.natDegree hU hx hc = Q := by
    apply GermCoefficientRealization.AnalyticLocal.polynomialRealization_injective x
    rw [ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.realize_polynomialOfFamily x P Q.natDegree hU hx hc (fun y hy => (hd y hy).le),
      ← hQrepr, ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.realize_polynomialOfFamily x P Q.natDegree hU₀ hx₀ hc₀
        (fun y hy => (hP₀ y hy).2.le)]
  refine ⟨b, S, ?_, ?_⟩
  · intro k hk
    rw [GermPolynomialCoefficients.AnalyticLocal.polynomialOfFamily_coeff]
    split_ifs
    · apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hremzero y hy k hk
    · rfl
  · have heQ : (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c Q).val =
        ((fun p : E × ℂ => (P p.1).eval p.2) : Germ (𝓝 (x, c)) ℂ) := by
      rw [← hQnew]
      exact GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm_family x c P Q.natDegree hU hx hc (fun y hy => (hd y hy).le)
    apply Subtype.ext
    change a.val = (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c S).val +
      (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c Q).val * (q : Germ (𝓝 (x, c)) ℂ)
    rw [← hFa, heQ, GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm_family x c A Q.natDegree hU hx hrem hSdeg]
    apply Germ.coe_eq.mpr
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hxcU] with p hp
    exact hdivision p.1 hp.1 p.2 hp.2

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialDivision.AnalyticLocal
