import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueDerivedComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomSource

/-! # All Thom Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AllThomSource.Constructions

noncomputable section

/-! All actual source cohomology groups identify with the corresponding relative Thom groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularSourceSheaf_exact_positive (n : ℕ) : (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z).ExactAt (n+1) := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace Z.regularAnalyticModel Z.regularAnalyticSpace
  exact ClosedSourceResolution.Constructions.closedSourceSheaf_positive_exact (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)
    Z.isClosedEmbedding_regularComplementInclusion n

theorem regularThomGoodShift_exact_positive (n : ℕ) :
    (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).ExactAt (n+1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (GoodShiftCohomology.Constructions.regularThomGoodShift_positive_homology_isZero Z (n+1) (Nat.succ_pos n))

def regularSourceSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)
    (ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
    (regularSourceSheaf_exact_positive Z) U n

def regularThomSectionsDerivedIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  FlasqueDerivedComparison.Constructions.flasqueResolutionDerivedCohomologyIso (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (regularThomGoodShift_exact_positive Z) U n

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomAllDegreeSectionsIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n :=
  regularSourceSectionsDerivedIso Z U n ≪≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).rightDerived n).mapIso
      (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) ≪≫
    (regularThomSectionsDerivedIso Z U n).symm

def regularSourceThomAllDegreeRelativeIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) (2+n) :=
  (ClosedSourceResolution.Constructions.closedSourceSheafSectionCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U n).symm ≪≫
    regularSourceThomAllDegreeSectionsIso Z a ha U n ≪≫ ThomShiftSections.Constructions.regularThomGoodShiftSectionsRelativeIso Z U n

theorem regularSourceThomAllDegreeRelativeIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    regularSourceThomAllDegreeRelativeIso Z a ha U n =
      regularSourceThomAllDegreeRelativeIso Z b hb U n := by
  unfold regularSourceThomAllDegreeRelativeIso regularSourceThomAllDegreeSectionsIso
  rw [ThomResolutionDiagram.Constructions.regularSourceThomZeroSheafIso_eq Z a b ha hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AllThomSource.Constructions
