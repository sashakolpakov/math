import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceNaturality

/-! # Source Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceOpenNaturality.Constructions.Construction

noncomputable section

/-! The actual supported source–Thom isomorphisms restrict coherently to open neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_open_naturality
    (O : Opens Z.regularAmbientSpace) {U W : Opens Z.regularAmbientSpace} (i : U ⟶ W) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
          (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
            Set Z.regularAnalyticSpace)).map ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).map i).op) n ≫
        (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O U n).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
            ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)).map i.op)
          ((2 * p)+n) := by
  exact SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) O W n)
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) O U n)
    (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha O W n)
    (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha O U n)
    (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O W n)
    (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O U n) _ _ _ _
    (HodgeConjecture.DegreeTwo.SupportOpenRestriction.Constructions.closedSourceSupportedRelativeCohomologyIso_open_naturality
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O i (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) n)
    (SupportChanges.Constructions.Construction.regularSourceThomClosedSupportIso_naturality Z a ha O W O U
      (HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions.closedSupportSectionRestriction (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O i) n)
    (IntersectOpenNaturality.Constructions.Construction.regularThomClosedSupportRelativeIso_open_naturality Z O i n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceOpenNaturality.Constructions.Construction
