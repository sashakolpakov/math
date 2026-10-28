import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCochain
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift

/-! # Support Sheaf Cup Shift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupShift.Constructions

noncomputable section

/-! The original supported cup cochain passes through the actual good-shift projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)
variable (he : ∀ n, n<2 → (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).ExactAt n)

def twoSupportThomGoodShiftIso :=
  ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftIso O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) 2 he

theorem closedSupportGoodShiftSheafCup_cochain (q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).X q) :
    (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map ((RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a).f q)
        ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) =
      (twoSupportThomGoodShiftIso C O U he).hom.f q
        (((GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).restrictionToTruncGE'
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)).f q
          ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f (2+q)
            (SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
              (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
              (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U).val b))) := by
  let K := CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let F := ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let c := (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f (2+q)
    (SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U).val b)
  have hp := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftIso_projection O U K
      (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) 2 he) q) c
  change (twoSupportThomGoodShiftIso C O U he).hom.f q
      (((GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)).f q c) =
    F.map ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)).f q) c at hp
  change F.map ((RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a).f q ≫
      (K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)).f q)
      ((ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) = _
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  exact (congrArg (F.map ((K.restrictionToTruncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2)).f q))
    (SupportSheafCupCochain.Constructions.closedSupportSheafCup_cochain C O U a q b)).trans hp.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupShift.Constructions
