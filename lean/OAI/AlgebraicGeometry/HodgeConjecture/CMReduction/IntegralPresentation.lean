import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectivePresentation
import OAI.AlgebraicGeometry.CycleClass.Geometric.ImageNaturality

/-! # Integral Presentation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegralPresentation.CM.Construction

noncomputable section

/-! Agreement of the two native cycle-image interfaces used by CMReduction.
On an integral variety its only component inclusion is an actual algebraic
isomorphism. This proves the comparison; it is not a new hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def integralComponentIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : irreducibleComponents V.carrier) :
    (V.presentation.componentVariety C).toOver ≅ V.toOver := by
  let f := V.presentation.componentInclusionOver C
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  have hi : IsIso f.left := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply SetLike.coe_injective
    change Set.range (V.presentation.componentInclusion C) = Set.univ
    rw [V.presentation.componentInclusion_range, hC]
  letI := hi
  exact Over.isoMk (asIso f.left) f.w

@[simp]
theorem integralComponentIso_hom (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : irreducibleComponents V.carrier) :
    (integralComponentIso V C).hom = V.presentation.componentInclusionOver C := rfl

theorem integral_presentation_geometricClasses (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    V.presentation.geometricAlgebraicClasses p = V.geometricAlgebraicClasses p := by
  ext a
  rw [V.presentation.mem_geometricAlgebraicClasses_iff_components]
  constructor
  · intro h
    let C : irreducibleComponents V.carrier :=
      ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
    have hc := h C
    rw [V.presentation.componentBettiEquiv_apply] at hc
    apply (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff
      (integralComponentIso V C) p a).mp
    simpa only [integralComponentIso_hom] using! hc
  · intro ha C
    rw [V.presentation.componentBettiEquiv_apply]
    have hc := (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_mem_geometricAlgebraicClasses_iff
      (integralComponentIso V C) p a).mpr ha
    simpa only [integralComponentIso_hom] using! hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IntegralPresentation.CM.Construction
