import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain

/-! # Small Sheaf Quasi Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallSheafQuasiIso.Constructions

noncomputable section

section

/-! The binary-small comparison computes the original union-relative cohomology in the supported sheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O U : Opens X)

def binaryOpenRelativeCochainMap :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ O : Opens X) : Set X) U) ⟶ BinarySmallSheafComparison.Constructions.binaryOpenSmallCochains C O U :=
  BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)

theorem binarySmallToIntersectSupportedSections_inclusion_apply (n : ℕ)
    (c : (BinarySmallSheafComparison.Constructions.binaryOpenSmallCochains C O U).X n) :
    (IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U).f n
      ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f n c) =
    (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f n
      (BinarySmallCochains.Constructions.binarySmallCochainInclusion (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) n c) := by
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U
  let B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U
  let g := BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap (TopCat.of U) A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft (TopCat.of U) A B)
  have hi := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections_inclusion C O U) n) c
  change (IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U).f n
      ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f n c) =
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X C U).f n
      ((AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X C U).f n (g.f n c)) at hi
  have hs := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections_inclusion (ModuleCat.of ℚ ℚ) X C U) n) (g.f n c)
  refine hi.trans (hs.trans ?_)
  change (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) A).f n (g.f n c)) = _
  exact congrArg ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f n)
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap_inclusion (TopCat.of U) A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft (TopCat.of U) A B)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection (TopCat.of U) A B) n c)

theorem binaryOpenRelativeCochainMap_supported_comparison :
    binaryOpenRelativeCochainMap C O U ≫ BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U =
      IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O U := by
  apply (cancel_mono (IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U)).mp
  rw [Category.assoc, IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_inclusion]
  ext n c
  change (IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U).f n
      ((BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U).f n ((binaryOpenRelativeCochainMap C O U).f n c)) =
    (AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f n
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ O : Opens X) : Set X) U)).f n c)
  rw [binarySmallToIntersectSupportedSections_inclusion_apply]
  exact congrArg ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U).f n)
    (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) n c)

instance binaryOpenRelativeCochainMap_quasiIso : QuasiIso (binaryOpenRelativeCochainMap C O U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact BinarySmallRelativeComparison.Constructions.binarySmallRelativeCohomologyMap_bijective (TopCat.of U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
    (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) n

variable [MetrizableSpace X]

instance binarySmallToIntersectSupportedSections_quasiIso :
    QuasiIso (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) := by
  have h : QuasiIso (binaryOpenRelativeCochainMap C O U ≫ BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) := by
    rw [binaryOpenRelativeCochainMap_supported_comparison]
    infer_instance
  exact quasiIso_of_comp_left (binaryOpenRelativeCochainMap C O U) _

end

/-! The original two-support cup is represented in the genuine intersection-support sheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [MetrizableSpace X] (C O U : Opens X)

theorem binarySmallSheafComparison_cohomology (n : ℕ) :
    HomologicalComplex.homologyMap (binaryOpenRelativeCochainMap C O U) n ≫
      HomologicalComplex.homologyMap (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) n ≫
        (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U n).hom = 𝟙 _ := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    binaryOpenRelativeCochainMap_supported_comparison, IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology]

theorem twoSupportCup_intersectedSheaf_class {p q : ℕ}
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U)) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)) q) :
    (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (p+q)).hom
      (HomologicalComplex.homologyMap (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) (p+q)
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q) (SupportCupCochain.Constructions.twoSupportSmallCupCocycle (TopCat.of U)
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) a b))) =
    SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U)
      (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) p q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b) := by
  let A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U
  let B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U
  let t := SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U) A B
    (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) p q
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b)
  have he := ConcreteCategory.congr_hom (binarySmallSheafComparison_cohomology C O U (p+q)) t
  change (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U (p+q)).hom
    (HomologicalComplex.homologyMap (BinarySmallSheafComparison.Constructions.binarySmallToIntersectSupportedSections C O U) (p+q)
      (HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap (TopCat.of U) A B) (p+q) t)) = t at he
  have hc := SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class (TopCat.of U) A B
    (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) a b
  change HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap (TopCat.of U) A B) (p+q) t = _ at hc
  rw [hc] at he
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmallSheafQuasiIso.Constructions
