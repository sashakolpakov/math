import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget

/-! # Support Sheaf Cup Cochain -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCochain.Constructions

noncomputable section

/-! Closed-support sections of the actual sheaf cup retain the literal two-support cup cochain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O U : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)

theorem closedSupportSheafCup_cochain (q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).X q) :
    (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map ((RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a).f q)
        ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) =
      (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f (2+q)
        (SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
          (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U).val b) := by
  let K := CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let g := (RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a).f q
  let aa := RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U
  let c := SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa.val b
  apply CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U (K.X (2+q))
  have hn := ConcreteCategory.congr_hom (ClosedSupportExactnessShift.Constructions.closedSectionInclusion_naturality O U g)
    ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)
  have hb := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections_inclusion O U) q) b
  have hu := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (RelativeCupSheaf.Constructions.relativeTwoCupSheafSectionsMap_unit X C a U) q)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)
  have hl := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections_left C O U) (2+q)) c
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hb hu hl
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g
    ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)) = _ at hu
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X (2+q))).hom.app (op U)
    ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f (2+q) c) =
    (BinarySmallSheafComparison.Constructions.binarySmallToLeftSupportedSections C O U).f (2+q) c at hl
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X (2+q))).hom.app (op U)
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map g ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) =
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X (2+q))).hom.app (op U)
      ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f (2+q) c)
  change (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X (2+q))).hom.app (op U)
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map g ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) =
    (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g
      ((ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).f q
        ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) at hn
  refine hn.trans ((congrArg ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g) hb).trans
    (hu.trans (Eq.trans ?_ hl.symm)))
  change (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f (2+q)
      (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) 2 q aa.val
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)) =
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f (2+q)
      ((BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft (TopCat.of U) _ _)).f (2+q) c)
  exact congrArg ((AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f (2+q))
    (SupportCupForget.Constructions.twoSupportSmallCup_forget_right (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa.val b).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCochain.Constructions
