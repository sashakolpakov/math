import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportSectionLift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallForgetSupport

/-! # Binary Small Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions

noncomputable section

/-! Genuine binary-small cochains map to the actual sheaf sections with both supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem binarySmallForget_inclusion_eq (X : TopCat.{0}) (A B : Set X) :
    BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A =
    BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B := by
  ext n c
  exact (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap_inclusion X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)
    (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection X A B) n c).trans
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap_inclusion X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection X A B) n c).symm

variable {X : TopCat.{0}} (C O U : Opens X)

abbrev binaryOpenSmallCochains := BinarySmallCochains.Constructions.binarySmallCochains (TopCat.of U)
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)

def binarySmallToLeftSupportedSections : binaryOpenSmallCochains C O U ⟶
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) :=
  BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft (TopCat.of U) _ _) ≫
    AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U

def binarySmallToRightSupportedSections : binaryOpenSmallCochains C O U ⟶
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X O) :=
  BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight (TopCat.of U) _ _) ≫
    AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U

theorem binarySmallSupportedSections_compatible :
    binarySmallToLeftSupportedSections C O U ≫ IntersectSupportSectionLift.Constructions.supportedSectionInclusion C U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) =
      binarySmallToRightSupportedSections C O U ≫ IntersectSupportSectionLift.Constructions.supportedSectionInclusion O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) := by
  change (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U) _ _ _ _ ≫
    AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U) ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X C U =
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U) _ _ _ _ ≫
      AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X O U) ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X O U
  simp only [Category.assoc, AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections_inclusion]
  simp only [← Category.assoc]
  exact congrArg (fun f => f ≫ AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U)
    (binarySmallForget_inclusion_eq (TopCat.of U) _ _)

def binarySmallToIntersectSupportedSections : binaryOpenSmallCochains C O U ⟶
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) :=
  IntersectSupportSectionLift.Constructions.intersectSupportSectionLift C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)
    (binarySmallToLeftSupportedSections C O U) (binarySmallToRightSupportedSections C O U)
    (binarySmallSupportedSections_compatible C O U)

theorem binarySmallToIntersectSupportedSections_left :
    binarySmallToIntersectSupportedSections C O U ≫
      ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) =
    binarySmallToLeftSupportedSections C O U :=
  IntersectSupportSectionLift.Constructions.intersectSupportSectionLift_left C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) _ _ _

theorem binarySmallToIntersectSupportedSections_inclusion :
    binarySmallToIntersectSupportedSections C O U ≫
      IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U =
    binarySmallToLeftSupportedSections C O U ≫ IntersectSupportSectionLift.Constructions.supportedSectionInclusion C U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) :=
  IntersectSupportSectionLift.Constructions.intersectSupportSectionLift_inclusion C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions
