import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceNaturality

/-! # Source Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SourceOpenNaturality.Constructions.HigherThom

noncomputable section

/-! The actual supported source–Thom isomorphisms restrict coherently to open neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_open_naturality
    (O : Opens Z.regularAmbientSpace) {U W : Opens Z.regularAmbientSpace} (i : U ⟶ W) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
          (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
            Set Z.regularAnalyticSpace)).map ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).map i).op) n ≫
        (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O U n).hom =
      (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
            ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)).map i.op)
          ((2 * p)+n) := by
  exact Supported.SourceNaturality.Constructions.HigherThom.sourceTargetIso_naturality
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) O W n)
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) O U n)
    (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha O W n)
    (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha O U n)
    (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O W n)
    (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n) _ _ _ _
    (HodgeConjecture.DegreeTwo.SupportOpenRestriction.Constructions.closedSourceSupportedRelativeCohomologyIso_open_naturality
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O i (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) n)
    (SupportChanges.Constructions.HigherThom.regularSourceThomClosedSupportIso_naturality Z a ha O W O U
      (HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions.closedSupportSectionRestriction (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O i) n)
    (HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality.Constructions.regularThomClosedSupportRelativeIso_open_naturality Z O i n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SourceOpenNaturality.Constructions.HigherThom
