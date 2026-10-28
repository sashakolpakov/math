import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges

/-! # Support Changes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportChanges

noncomputable section

/-! Naturality of the higher-codimension Thom comparison in specified supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges.Constructions
set_option backward.isDefEq.respectTransparency false
namespace Constructions.HigherThom

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
variable {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

include ha in
theorem regularSourceThomClosedSupportIso_naturality
    (O U P W : Opens Z.regularAmbientSpace)
    (α : HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U ⟶
      HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor P W) (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z)) n ≫ (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha P W n).hom =
      (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha O U n).hom ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
          (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)) n :=
  HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions.closedSupportDerivedResolutionIso_functor_naturality (X := TopCat.of Z.regularAmbientSpace)
    O U P W α (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)) (AllDegreeSource.Constructions.HigherThom.regularSourceSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z) (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z)
    (AllDegreeSource.Constructions.HigherThom.regularThomGoodShift_exact_positive Z) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceThomZeroSheafIso Z a ha) n

end Constructions.HigherThom

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportChanges
