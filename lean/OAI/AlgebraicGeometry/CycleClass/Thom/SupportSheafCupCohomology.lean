import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupShift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallSheafQuasiIso

/-! # Support Sheaf Cup Cohomology -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCohomology.Constructions.Even

noncomputable section

/-! The supported sheaf cup induces the original two-support cup on actual relative cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallSheafQuasiIso.Constructions

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) (2 * p))
variable (he : ∀ n, n<(2 * p) → (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).ExactAt n)

def twoSupportThomRelativeIso (n : ℕ) :=
  HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso O U (Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)
      (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) (2 * p) he n ≪≫
    HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U ((2 * p)+n)

theorem closedSupportGoodShiftSheafCup_cohomology (q : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q ≫
      HomologicalComplex.homologyMap
        (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap X C a)) q ≫
        (twoSupportThomRelativeIso C O U he q).hom =
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) (2 * p) q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)) q b
  let K := Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let F := HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let aa := EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction X (C : Set X) a U
  let c := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) ((2 * p)+q)
    (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCocycle (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa b)
  have hc : AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap X C a)) q
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q b) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (SupportSheafCupShift.Constructions.Even.twoSupportThomGoodShiftIso C O U he).hom q
      (HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (2 * p) q c) := by
    apply Subtype.ext
    exact SupportSheafCupShift.Constructions.Even.closedSupportGoodShiftSheafCup_cochain C O U a he q b.val
  simp only [ConcreteCategory.comp_apply]
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change (twoSupportThomRelativeIso C O U he q).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap X C a)) q
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q b))) = _
  rw [hc]
  change (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U ((2 * p)+q)).hom
    ((HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso O U K
      (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) (2 * p) he q).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (SupportSheafCupShift.Constructions.Even.twoSupportThomGoodShiftIso C O U he).hom q
        (HodgeConjecture.DegreeTwo.GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex F K) (2 * p) q c)))) = _
  refine (congrArg (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U ((2 * p)+q)).hom
    (HodgeConjecture.DegreeTwo.ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso_class O U K
      (Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) (2 * p) he q c)).trans ?_
  change (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U ((2 * p)+q)).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ ((2 * p)+q) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (HodgeConjecture.DegreeTwo.BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) ((2 * p)+q)
      (HodgeConjecture.DegreeTwo.SupportCupCochain.Constructions.twoSupportSmallCupCocycle (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa b))) = _
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact HodgeConjecture.DegreeTwo.SmallSheafQuasiIso.Constructions.twoSupportCup_intersectedSheaf_class C O U aa b

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCohomology.Constructions.Even
