import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkValues
import OAI.AlgebraicGeometry.Comparison.Betti.RegularStalkUnits

/-! # Concrete Holomorphic Stalk Local -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkLocal

noncomputable section

/-! The original analytification structure morphism is a local ring
homomorphism on actual stalks, with its original section evaluations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkValues.AnalyticLocal

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem algebraicHolomorphicStalkMap_germ_value (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (U : X.left.Opens)
    (hp : Analytification.Base.analytificationMap X p ∈ U) (s : Γ(X.left, U)) :
    Holomorphic.StalkValues.AnalyticLocal.manifoldStalkValue p
      (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s)) =
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue p.left U hp s :=
  (congrArg (Holomorphic.StalkValues.AnalyticLocal.manifoldStalkValue p) (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap_germ X p U hp s)).trans
    ((Holomorphic.StalkValues.AnalyticLocal.manifoldStalkValue_germ p (Open.AffineIsoEvaluation.analyticOpen X U) hp (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s)).trans
      (RegularStalkUnits.sectionEvaluationOn_complexSectionValue X U s ⟨p, hp⟩))

instance algebraicHolomorphicStalkMap_isLocalHom (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    IsLocalHom (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p) where
  map_nonunit a ha := by
    obtain ⟨U, hp, s, rfl⟩ := X.left.presheaf.exists_germ_eq a
    have hv := (Holomorphic.StalkValues.AnalyticLocal.manifoldStalk_isUnit_iff p _).mp ha
    rw [algebraicHolomorphicStalkMap_germ_value] at hv
    exact RegularStalkUnits.regular_germ_isUnit_of_value p.left U hp s hv

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkLocal
