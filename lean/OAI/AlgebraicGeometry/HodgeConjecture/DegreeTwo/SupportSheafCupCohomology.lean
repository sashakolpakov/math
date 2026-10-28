import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupShift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallSheafQuasiIso

/-! # Support Sheaf Cup Cohomology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCohomology.Constructions

noncomputable section

/-! The supported sheaf cup induces the original two-support cup on actual relative cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)
variable (he : ∀ n, n<2 → (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).ExactAt n)

def twoSupportThomRelativeIso (n : ℕ) :=
  ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso O U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)
      (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) 2 he n ≪≫
    SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (2+n)

theorem closedSupportGoodShiftSheafCup_cohomology (q : ℕ) :
    HomologicalComplex.homologyMap (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q ≫
      HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a)) q ≫
        (twoSupportThomRelativeIso C O U he q).hom =
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) 2 q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)) q b
  let K := CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C
  let F := ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U
  let aa := RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction X (C : Set X) a U
  let c := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) (2+q)
    (SupportCupCochain.Constructions.twoSupportSmallCupCocycle (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa b)
  have hc : AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a)) q
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q b) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (SupportSheafCupShift.Constructions.twoSupportThomGoodShiftIso C O U he).hom q
      (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (GoodShiftFunctor.Constructions.functorCochainComplex F K) 2 q c) := by
    apply Subtype.ext
    exact SupportSheafCupShift.Constructions.closedSupportGoodShiftSheafCup_cochain C O U a he q b.val
  simp only [ConcreteCategory.comp_apply]
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change (twoSupportThomRelativeIso C O U he q).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a)) q
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) q b))) = _
  rw [hc]
  change (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (2+q)).hom
    ((ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso O U K
      (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) 2 he q).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (SupportSheafCupShift.Constructions.twoSupportThomGoodShiftIso C O U he).hom q
        (GoodShiftRepresentatives.Constructions.cochainGoodShiftCocycle (GoodShiftFunctor.Constructions.functorCochainComplex F K) 2 q c)))) = _
  refine (congrArg (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (2+q)).hom
    (ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso_class O U K
      (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X C) 2 he q c)).trans ?_
  change (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (2+q)).hom
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+q) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) (2+q)
      (SupportCupCochain.Constructions.twoSupportSmallCupCocycle (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) aa b))) = _
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact SmallSheafQuasiIso.Constructions.twoSupportCup_intersectedSheaf_class C O U aa b

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSheafCupCohomology.Constructions
