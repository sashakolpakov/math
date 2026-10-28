import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality

/-! # Source Thom Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen.Constructions

noncomputable section

/-! The actual supported source–Thom isomorphisms restrict coherently to open neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_open_naturality
    (O : Opens Z.regularAmbientSpace) {U W : Opens Z.regularAmbientSpace} (i : U ⟶ W) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
          (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
            Set Z.regularAnalyticSpace)).map ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).map i).op) n ≫
        (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U n).hom =
      (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
            ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)).map i.op)
          (2+n) := by
  exact SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O W n)
    (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O U n)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha O W n)
    (ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso Z a ha O U n)
    (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O W n)
    (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n) _ _ _ _
    (SupportOpenRestriction.Constructions.closedSourceSupportedRelativeCohomologyIso_open_naturality
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O i (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) n)
    (SupportSectionChanges.Constructions.regularSourceThomClosedSupportIso_naturality Z a ha O W O U
      (SupportSectionChanges.Constructions.closedSupportSectionRestriction (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O i) n)
    (IntersectSupportOpenNaturality.Constructions.regularThomClosedSupportRelativeIso_open_naturality Z O i n)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen.Constructions
