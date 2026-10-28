import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift

/-! # Supported Relative -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedRelative.Constructions.Construction

noncomputable section

/-! The actual closed-complex-immersion Thom comparison retains the specified support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions
set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

def regularThomClosedSupportRelativeIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex
      (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U)
      (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U)
      (2*p+n) :=
  HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso (X := TopCat.of Z.regularAmbientSpace) O U Z.regularThomSheafComplex
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z i (by omega)) n ≪≫
    HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso (X := TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen O U (2*p+n)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedRelative.Constructions.Construction
