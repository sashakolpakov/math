import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialNe
import OAI.AlgebraicGeometry.Comparison.Betti.GermPolynomialCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.DistinguishedPreparation

/-! # Germ Preparation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermPreparation.AnalyticLocal

noncomputable section

/-! Weierstrass preparation in the actual ring of holomorphic germs,
with a unit and a monic polynomial whose central coefficients are fixed. -/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def verticalRestriction (x : E) (c : ℂ) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm c :=
  Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition (fun z : ℂ => (x, z))
    ((differentiable_const x).prodMk differentiable_id) c

theorem germ_weierstrass_preparation {n : ℕ} (x : Fin n → ℂ) (c : ℂ)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) (ha : verticalRestriction x c a ≠ 0) :
    ∃ (P : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (u : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)),
      P.Monic ∧ P.map (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) = (X - C c) ^ P.natDegree ∧ IsUnit u ∧
      a = GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c P * u := by
  obtain ⟨F, hFa, W, hW, hxc, hF⟩ := a.property
  have hn : ¬∀ᶠ z in 𝓝 c, F (x, z) = 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    change GermComposition.AnalyticLocal.germComposition (fun z : ℂ => (x, z)) _ a.val = 0
    rw [← hFa]
    exact Germ.coe_eq.mpr hz
  obtain ⟨R, d, U, P, q, hR, hU, hx, hcoeff, hP, hcenter, hq, hqn, hfactor⟩ :=
    DistinguishedPreparation.Weierstrass.exists_distinguished_preparation hW hF hxc hn
  let Q := ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialOfFamily x P d hU hx hcoeff
  have hQ := GermPolynomialCoefficients.AnalyticLocal.polynomialOfFamily_monic_degree x P d hU hx hcoeff hP
  have hxcU : (x, c) ∈ U ×ˢ ball c R := ⟨hx, mem_ball_self hR⟩
  let u := ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction (x, c) q (hU.prod isOpen_ball) hxcU hq
  refine ⟨Q, u, hQ.1, ?_, ?_, ?_⟩
  · rw [GermPolynomialCoefficients.AnalyticLocal.polynomialOfFamily_map_value x P d hU hx hcoeff ((hP x hx).2.le), hcenter, hQ.2]
  · exact (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.isUnit_iff_value_ne_zero (x, c) u).mpr (hqn (x, c) hxcU)
  · apply Subtype.ext
    change a.val = (GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm x c Q).val * (q : Germ (𝓝 (x, c)) ℂ)
    rw [← hFa, GermPolynomialNe.AnalyticLocal.polynomialEvaluationGerm_family x c P d hU hx hcoeff
      (fun y hy => (hP y hy).2.le)]
    apply Germ.coe_eq.mpr
    filter_upwards [(hU.prod isOpen_ball).mem_nhds hxcU] with p hp
    exact hfactor p hp

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermPreparation.AnalyticLocal
