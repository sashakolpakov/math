import OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendComponentProjectiveMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentCohomologyExtension

/-! # Extended Projective -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedProjective

noncomputable section

/-! The extended actual projective morphism realizes extension by zero of its original component Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem extendedProjectiveChernClass (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents P.carrier) {n : ℕ}
    (g : (P.componentVariety C).toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) :
    First.firstChernClassQ P (GeneratingLineBundle.generatingAlgebraicLineBundle P (ExtendComponentProjectiveMap.extendComponentProjectiveMap P C g)) =
      ComponentCohomologyExtension.componentCohomologyExtension P C
        (First.firstChernClassQ (P.componentVariety C).presentation
          (GeneratingLineBundle.generatingAlgebraicLineBundle (P.componentVariety C).presentation g)) := by
  classical
  apply (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
  rw [ComponentCohomologyExtension.componentCohomologyExtension_components]
  funext D
  have hc : P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2
        (First.firstChernClassQ P (GeneratingLineBundle.generatingAlgebraicLineBundle P (ExtendComponentProjectiveMap.extendComponentProjectiveMap P C g))) D =
      First.firstChernClassQ (P.componentVariety D).presentation
        (GeneratingLineBundle.generatingAlgebraicLineBundle (P.componentVariety D).presentation
          (P.componentInclusionOver D ≫ ExtendComponentProjectiveMap.extendComponentProjectiveMap P C g)) := by
    rw [P.componentBettiEquiv_apply]
    exact (GeneratingNaturality.generatingAlgebraicLineBundle_firstChern_naturality
      (P.componentInclusionOver D) (ExtendComponentProjectiveMap.extendComponentProjectiveMap P C g)).symm
  rw [hc]
  by_cases hDC : D = C
  · subst D
    rw [ExtendComponentProjectiveMap.extendComponentProjectiveMap_self, Pi.single_eq_same]
  · rw [ExtendComponentProjectiveMap.extendComponentProjectiveMap_other P C g D hDC, ConstantProjectiveMap.constantProjectiveMap_firstChern_zero]
    simp only [Pi.single_eq_of_ne hDC]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedProjective
