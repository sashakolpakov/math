import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomResolutionDiagram

/-! # Regular Thom Source Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSections.Constructions

noncomputable section

/-! The independent source cohomology and actual relative Thom group agree on every open set. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomSectionsZeroIso (U : Opens Z.regularAmbientSpace) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)).homology 0 ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology 0 :=
  RegularThomSourceSheaf.Constructions.zeroSectionComparisonIso
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U)
    (RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z)
    (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z) (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha)

/-- This comparison intertwines the native source pullback and the actual sheaf cup. -/
theorem regularSourceThomSectionsZeroIso_comm (U : Opens Z.regularAmbientSpace) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) 0 ≫
        (regularSourceThomSectionsZeroIso Z a ha U).hom =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
            Z.regularThomComplementOpen a)) 0 :=
  RegularThomSourceSheaf.Constructions.zeroSectionComparisonIso_comm
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U)
    (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
    (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a)
    (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha)
    (RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm Z a ha)

def regularSourceThomRelativeSectionsIso (U : Opens Z.regularAmbientSpace) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) 0 ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) 2 :=
  (ClosedSourceResolution.Constructions.closedSourceSheafSectionCohomologyIso (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U 0).symm ≪≫
    regularSourceThomSectionsZeroIso Z a ha U ≪≫ ThomShiftSections.Constructions.regularThomGoodShiftSectionsRelativeIso Z U 0

theorem regularSourceThomRelativeSectionsIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (U : Opens Z.regularAmbientSpace) :
    regularSourceThomRelativeSectionsIso Z a ha U = regularSourceThomRelativeSectionsIso Z b hb U := by
  unfold regularSourceThomRelativeSectionsIso regularSourceThomSectionsZeroIso
  rw [ThomResolutionDiagram.Constructions.regularSourceThomZeroSheafIso_eq Z a b ha hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSections.Constructions
