import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupSheaf
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget

/-! # Support Sheaf Cup Cochain -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCochain.Constructions.Even

noncomputable section

/-! Closed-support sections of the actual sheaf cup retain the literal two-support cup cochain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O U : Opens X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) (2 * p))

theorem closedSupportSheafCup_cochain (q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).X q) :
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map ((EvenCupSheaf.Constructions.relativeEvenCupSheafMap X C a).f q)
        ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) =
      (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f ((2 * p)+q)
        (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
          (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U).val b) := by
  let K := Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let g := (EvenCupSheaf.Constructions.relativeEvenCupSheafMap X C a).f q
  let aa := EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U
  let c := HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa.val b
  apply Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U (K.X ((2 * p)+q))
  have hn := ConcreteCategory.congr_hom (HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSectionInclusion_naturality O U g)
    ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)
  have hb := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections_inclusion O U) q) b
  have hu := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (EvenCupSheaf.Constructions.relativeEvenCupSheafSectionsMap_unit X C a U) q)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)
  have hl := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections_left C O U) ((2 * p)+q)) c
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hb hu hl
  change (Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g
    ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f q
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)) = _ at hu
  change (Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X ((2 * p)+q))).hom.app (op U)
    ((HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f ((2 * p)+q) c) =
    (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToLeftSupportedSections C O U).f ((2 * p)+q) c at hl
  change (Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X ((2 * p)+q))).hom.app (op U)
      ((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map g ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) =
    (Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X ((2 * p)+q))).hom.app (op U)
      ((HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f ((2 * p)+q) c)
  change (Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X ((2 * p)+q))).hom.app (op U)
      ((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map g ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) =
    (Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g
      ((HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).f q
        ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b)) at hn
  refine hn.trans ((congrArg ((Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).map g) hb).trans
    (hu.trans (Eq.trans ?_ hl.symm)))
  change (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f ((2 * p)+q)
      (Geometric.RelativeCup.Cycles.relativeAbsoluteCup (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (2 * p) q aa.val
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).f q b)) =
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f ((2 * p)+q)
      ((HodgeConjecture.DegreeTwo.BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft (TopCat.of U) _ _)).f ((2 * p)+q) c)
  exact congrArg ((AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f ((2 * p)+q))
    (HodgeConjecture.DegreeTwo.SupportCupForget.Constructions.twoSupportSmallCup_forget_right (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa.val b).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCochain.Constructions.Even
