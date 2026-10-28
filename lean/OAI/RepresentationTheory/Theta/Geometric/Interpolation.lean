import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Interpolation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Interpolation.RiemannProjectivityConstruction

noncomputable section

/-! Theta coordinates interpolate a prescribed nonzero value and finitely
many zeros at distinct period points. -/

open scoped BigOperators

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Λ : AddSubgroup V}

namespace ThetaSection

def _root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection.finiteProduct {I : Type} [Fintype I] {n : ℕ} (t : I → Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Λ n) :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Λ (n * Fintype.card I) where
  toFun z := ∏ i, t i z
  regular := contDiff_prod (fun i _ => (t i).regular)
  translates l z := by
    simp only [(t _).translates, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, pow_mul]

end ThetaSection

namespace FiniteSectionFamily

variable (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily H Λ) (hF : Function.Injective F.projectiveMap)

include hF

theorem _root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily.exists_section_vanish (p q : V)
    (hpq : (QuotientAddGroup.mk p : V ⧸ Λ) ≠ QuotientAddGroup.mk q) :
    ∃ t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Λ F.degree, t p ≠ 0 ∧ t q = 0 := by
  have hsep : F.Separates p q := by
    by_contra hn
    exact hpq (hF ((F.projectiveMap_eq_of_not_separates p q).mpr hn))
  obtain ⟨s, _, t, _, hst⟩ := hsep
  refine ⟨(s.constMul (t q)).add (t.constMul (-s q)), ?_, ?_⟩
  · change t q * s p + -s q * t p ≠ 0
    intro hz
    apply hst
    linear_combination hz
  · change t q * s q + -s q * t q = 0
    ring

theorem _root_.OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily.exists_section_vanish_finite {I : Type} [Fintype I] (p : V) (q : I → V)
    (hpq : ∀ i, (QuotientAddGroup.mk p : V ⧸ Λ) ≠ QuotientAddGroup.mk (q i)) :
    ∃ t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Λ (F.degree * Fintype.card I), t p ≠ 0 ∧ ∀ i, t (q i) = 0 := by
  classical
  choose t htp htq using fun i => F.exists_section_vanish hF p (q i) (hpq i)
  refine ⟨Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection.finiteProduct t, ?_, ?_⟩
  · change ∏ i, t i p ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => htp i)
  intro i
  change ∏ j, t j (q i) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact htq i

end FiniteSectionFamily

end

end OAI.RepresentationTheory.Theta.Geometric.Interpolation.RiemannProjectivityConstruction
