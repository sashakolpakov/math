import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCochain
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift

/-! # Support Sheaf Cup Shift -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupShift.Constructions.Even

noncomputable section

/-! The original supported cup cochain passes through the actual good-shift projection. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) (2 * p))
variable (he : ∀ n, n<(2 * p) → (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).ExactAt n)

def twoSupportThomGoodShiftIso :=
  HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftIso O U (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)
    (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) (2 * p) he

theorem closedSupportGoodShiftSheafCup_cochain (q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)).X q) :
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).map ((EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap X C a).f q)
        ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) =
      (twoSupportThomGoodShiftIso C O U he).hom.f q
        (((HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
          (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).restrictionToTruncGE'
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))).f q
          ((HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f ((2 * p)+q)
            (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
              (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
              (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U).val b))) := by
  let K := Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let F := HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let c := (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f ((2 * p)+q)
    (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCochain (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U).val b)
  have hp := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftIso_projection O U K
      (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) (2 * p) he) q) c
  change (twoSupportThomGoodShiftIso C O U he).hom.f q
      (((HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K).restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))).f q c) =
    F.map ((K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))).f q) c at hp
  change F.map ((EvenCupSheaf.Constructions.relativeEvenCupSheafMap X C a).f q ≫
      (K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))).f q)
      ((HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U).f q b) = _
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  exact (congrArg (F.map ((K.restrictionToTruncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p))).f q))
    (SupportSheafCupCochain.Constructions.Even.closedSupportSheafCup_cochain C O U a q b)).trans hp.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupShift.Constructions.Even
