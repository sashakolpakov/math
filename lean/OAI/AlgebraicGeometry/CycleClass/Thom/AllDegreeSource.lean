import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SourceSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque

/-! # All Degree Source -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AllDegreeSource.Constructions.HigherThom

noncomputable section

/-! All actual source cohomology groups identify with the corresponding relative Thom groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularAmbientSingularSheaf_exact_positive (n : ℕ) :
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel Z.regularAmbientSpace
  exact HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact (TopCat.of Z.regularAmbientSpace) n

theorem regularAmbientSingularSheaf_isFlasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).X n) :=
  AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) n

theorem regularSourceSheaf_exact_positive (n : ℕ) : (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace Z.regularAnalyticModel Z.regularAnalyticSpace
  exact HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_positive_exact (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)
    Z.isClosedEmbedding_regularComplementInclusion n

theorem regularThomGoodShift_exact_positive (n : ℕ) :
    (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).ExactAt (n+1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShift_positive_homology_isZero Z (n+1) (Nat.succ_pos n))

def regularSourceSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z))
    (regularSourceSheaf_exact_positive Z) U n

def regularThomSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (regularThomGoodShift_exact_positive Z) U n

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomAllDegreeSectionsIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z)).homology n ≅
      (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n :=
  regularSourceSectionsDerivedIso Z U n ≪≫
    ((Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).rightDerived n).mapIso
      (Regular.SourceSheaf.Constructions.HigherThom.regularSourceThomZeroSheafIso Z a ha) ≪≫
    (regularThomSectionsDerivedIso Z U n).symm

def regularSourceThomAllDegreeRelativeIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) ((2 * p)+n) :=
  (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheafSectionCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U n).symm ≪≫
    regularSourceThomAllDegreeSectionsIso Z a ha U n ≪≫ HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions.regularThomGoodShiftSectionsRelativeIso Z U n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AllDegreeSource.Constructions.HigherThom
