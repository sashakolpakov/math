import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallForgetSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology

/-! # Support Cup Forget -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget.Constructions

noncomputable section

/-! Forgetting either support of the genuine two-support cup recovers the corresponding native relative cup. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X)

theorem twoSupportSmallCup_forget_left {p q : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B)).f (p+q)
      (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b) =
    CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup X B p q ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a) b := by
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X B (p+q)
  rw [BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap_inclusion X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B)
    (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection X A B), SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion]
  exact (CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_inclusion X B
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a) b).symm

theorem twoSupportSmallCup_forget_right {p q : ℕ}
    (a : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q) :
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)).f (p+q)
      (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a b) =
    CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A p q a ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b) := by
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X A (p+q)
  rw [BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap_inclusion X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)
    (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection X A B), SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion]
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion X A
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) a ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b)).symm

theorem twoSupportCohomologyCup_forget_left (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (A := B) (B := A ∪ B) Set.subset_union_right (p+q)
      (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X B p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A p a) b := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q b
  have hm := congrArg (fun g => HomologicalComplex.homologyMap g (p+q))
    (BinarySmallForgetSupport.Constructions.binarySmallRelativeCochainMap_forget X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight_projection X A B) Set.subset_union_right)
  rw [HomologicalComplex.homologyMap_comp] at hm
  change HomologicalComplex.homologyMap (AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X
    (Set.subset_union_right : B ⊆ A ∪ B)) (p+q) _ = _
  rw [← hm]
  change HomologicalComplex.homologyMap
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B B (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B)) (p+q)
    (HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q) _) = _
  rw [SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change _ = CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X B p q
    (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) p
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a)) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b)
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) (p+q))
  apply Subtype.ext
  exact twoSupportSmallCup_forget_left X A B a.val b.val

theorem twoSupportCohomologyCup_forget_right (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X)
      (A := A) (B := A ∪ B) Set.subset_union_left (p+q)
      (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) =
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X B q b) := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p a
  obtain ⟨b,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q b
  have hm := congrArg (fun g => HomologicalComplex.homologyMap g (p+q))
    (BinarySmallForgetSupport.Constructions.binarySmallRelativeCochainMap_forget X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)
      (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft_projection X A B) Set.subset_union_left)
  rw [HomologicalComplex.homologyMap_comp] at hm
  change HomologicalComplex.homologyMap (AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X
    (Set.subset_union_left : A ⊆ A ∪ B)) (p+q) _ = _
  rw [← hm]
  change HomologicalComplex.homologyMap
    (BinarySmallForgetSupport.Constructions.binarySmallCochainToRelativeMap X A B A (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B)) (p+q)
    (HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q) _) = _
  rw [SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change _ = CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) X A p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a)
    (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B) q
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b))
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (p+q))
  apply Subtype.ext
  exact twoSupportSmallCup_forget_right X A B a.val b.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget.Constructions
