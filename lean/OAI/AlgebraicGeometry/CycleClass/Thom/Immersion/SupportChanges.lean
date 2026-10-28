import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ClosedSupportResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges

/-! # Support Changes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportChanges

noncomputable section

/-! Naturality of the higher-codimension Thom comparison in specified supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions
set_option backward.isDefEq.respectTransparency false
namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold}
variable {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

include ha in
theorem regularSourceThomClosedSupportIso_naturality
    (O U P W : Opens Z.regularAmbientSpace)
    (α : HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U ⟶
      HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor P W) (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (SourceSheaf.Constructions.Construction.regularSourceSheafComplex Z)) n ≫ (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha P W n).hom =
      (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha O U n).hom ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)) n :=
  HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions.closedSupportDerivedResolutionIso_functor_naturality (X := TopCat.of Z.regularAmbientSpace)
    O U P W α (SourceSheaf.Constructions.Construction.regularSourceSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)) (AllDegreeSource.Constructions.Construction.regularSourceSheaf_exact_positive Z)
    (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z) (ShiftSections.Constructions.Construction.regularThomGoodShift_isFlasque Z)
    (AllDegreeSource.Constructions.Construction.regularThomGoodShift_exact_positive Z) (SourceSheaf.Constructions.Construction.regularSourceThomZeroSheafIso Z a ha) n

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportChanges
