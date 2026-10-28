import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportComplex

/-! # Supported Thom Relative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions

noncomputable section

/-! The supported Thom resolution computes ambient relative cohomology with the exact intersection support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)

def intersectSupportedRelativeCohomologyIso (n : ℕ) :
    (GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U)
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ O : Opens X) : Set X) U) n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X (C ⊔ O) U
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) ≪≫
    (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X (C ⊔ O) U) n).symm

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularThomClosedSupportRelativeIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (GoodShiftFunctor.Constructions.functorCochainComplex
      (ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U)
      (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U)
      (2*p+n) :=
  ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso (X := TopCat.of Z.regularAmbientSpace) O U Z.regularThomSheafComplex
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) n ≪≫
    intersectSupportedRelativeCohomologyIso (X := TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen O U (2*p+n)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions
