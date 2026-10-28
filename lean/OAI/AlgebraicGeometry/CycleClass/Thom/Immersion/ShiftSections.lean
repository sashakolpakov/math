import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift

/-! # Shift Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ShiftSections.Constructions.Construction

noncomputable section

/-! The shifted supported complex of an actual closed complex immersion is
flasque and computes the actual relative groups on every open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

def regularThomGoodShiftSectionCohomologyIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)).homology n ≅
      (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        Z.regularThomComplementOpen U).homology (2*p+n) :=
  HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions.rationalFlasqueGoodShiftSectionCohomologyIso Z.regularThomSheafComplex
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z i (by omega)) U n

/-- Every open set retains its actual relative singular cohomology after the shift. -/
def regularThomGoodShiftSectionsRelativeIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) (2*p+n) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen U
  exact regularThomGoodShiftSectionCohomologyIso Z U n ≪≫
    (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen U) (2*p+n)).symm

/-- Global sections compute the original support cohomology in every shifted degree. -/
def regularThomGoodShiftGlobalRelativeIso (n : ℕ) :
    (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex (⊤ : Opens Z.regularAmbientSpace)
      (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ (2*p+n) :=
  regularThomGoodShiftSectionCohomologyIso Z ⊤ n ≪≫
    (Geometric.GlobalSupportPurity.Cycles.relativeSupportedGlobalCohomologyIso (TopCat.of Z.regularAmbientSpace)
      Z.regularThomComplementOpen (2*p+n)).symm

theorem regularThomGoodShift_isFlasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z).X n) :=
  HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.rationalGoodShift_isFlasque Z.regularThomSheafComplex
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z i (by omega)) n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ShiftSections.Constructions.Construction
