import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Source Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceIso.Constructions.HigherThom

noncomputable section

/-! The source–Thom isomorphism with a prescribed closed support, on the original relative groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomSupportedRelativeIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
        (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
          Set Z.regularAnalyticSpace) ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U)
      ((2 * p)+n) :=
  (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) O U n).symm ≪≫
    Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha O U n ≪≫ HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceIso.Constructions.HigherThom
