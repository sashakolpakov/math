import OAI.AlgebraicGeometry.Betti.ProjectivePresentationComparison
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Integral Pieces -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralPieces.CM.Abelian

noncomputable section

/-! The componentwise Hodge subspaces agree with the integral variety's native ones. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem integralComponentInclusion_isIso (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : irreducibleComponents X.carrier) :
    IsIso (X.presentation.componentInclusion C) := by
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ?_⟩
  apply (surjective_iff _).mpr
  apply Set.range_eq_univ.mp
  rw [X.presentation.componentInclusion_range, hC]

def integralComponentIso (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : irreducibleComponents X.carrier) :
    (X.presentation.componentVariety C).toOver ≅ X.toOver := by
  exact Over.isoMk (@asIso _ _ _ _ (X.presentation.componentInclusion C)
    (integralComponentInclusion_isIso X C))
    (X.presentation.componentInclusion_over C)

theorem integralPresentation_pureBettiSubspace (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    X.presentation.pureBettiSubspace p q = X.pureBettiSubspace p q := by
  ext a
  rw [X.presentation.mem_pureBettiSubspace_iff]
  constructor
  · intro ha
    let C : irreducibleComponents X.carrier :=
      ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
    have hc := ha C
    rw [X.presentation.componentBettiEquiv_apply] at hc
    exact (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace_iff
      (integralComponentIso X C) p q a).mp hc
  · intro ha C
    rw [X.presentation.componentBettiEquiv_apply]
    exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace
      (X.presentation.componentInclusionOver C) p q ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntegralPieces.CM.Abelian
