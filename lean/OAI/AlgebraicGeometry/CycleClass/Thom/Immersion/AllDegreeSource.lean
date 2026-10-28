import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceSheaf
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ShiftSections

/-! # All Degree Source -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.AllDegreeSource.Constructions.Construction

noncomputable section

/-! All actual source cohomology groups identify with the corresponding relative Thom groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem regularAmbientSingularSheaf_exact_positive (n : ℕ) :
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel Z.regularAmbientSpace
  exact HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact (TopCat.of Z.regularAmbientSpace) n

theorem regularAmbientSingularSheaf_isFlasque (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace)).X n) :=
  AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) n

theorem regularSourceSheaf_exact_positive (n : ℕ) : (SourceSheaf.Constructions.Construction.regularSourceSheafComplex Z).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace Z.regularAnalyticModel Z.regularAnalyticSpace
  exact HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_positive_exact (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)
    Z.isClosedEmbedding_regularComplementInclusion n

theorem regularThomGoodShift_exact_positive (n : ℕ) :
    (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z).ExactAt (n+1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (GoodShift.Constructions.Construction.regularThomGoodShift_positive_homology_isZero Z (n+1) (Nat.succ_pos n))

def regularSourceSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z))
    (regularSourceSheaf_exact_positive Z) U n

def regularThomSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)
    (ShiftSections.Constructions.Construction.regularThomGoodShift_isFlasque Z) (regularThomGoodShift_exact_positive Z) U n

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomAllDegreeSectionsIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (SourceSheaf.Constructions.Construction.regularSourceSheafComplex Z)).homology n ≅
      (Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShift.Constructions.Construction.regularThomGoodShiftSheafComplex Z)).homology n :=
  regularSourceSectionsDerivedIso Z U n ≪≫
    ((Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).rightDerived n).mapIso
      (SourceSheaf.Constructions.Construction.regularSourceThomZeroSheafIso Z a ha) ≪≫
    (regularThomSectionsDerivedIso Z U n).symm

def regularSourceThomAllDegreeRelativeIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) ((2 * p)+n) :=
  (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheafSectionCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U n).symm ≪≫
    regularSourceThomAllDegreeSectionsIso Z a ha U n ≪≫ ShiftSections.Constructions.Construction.regularThomGoodShiftSectionsRelativeIso Z U n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.AllDegreeSource.Constructions.Construction
