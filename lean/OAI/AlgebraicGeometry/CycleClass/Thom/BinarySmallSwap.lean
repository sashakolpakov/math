import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison
import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

/-! # Binary Small Swap -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions

noncomputable section

/-! Swapping the two vanishing conditions preserves the actual ambient cochain. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) (A B : Set X)

def binarySwapFn (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X B A).X n) : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).X n :=
  HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainLift X A B n (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X B A n c)
    (HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X B A A
      (Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X B A) n c)
    (HodgeConjecture.DegreeTwo.BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X B A B
      (Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X B A) n c)

theorem binarySwapFn_inclusion (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X B A).X n) :
    HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n (binarySwapFn X A B n c) =
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X B A n c := HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion X A B n _ _ _

def binarySwap : HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X B A ⟶ HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B where
  f n := ModuleCat.ofHom {
    toFun := binarySwapFn X A B n
    map_add' := by
      intro a b
      apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
      simp only [map_add, binarySwapFn_inclusion X A B n]
    map_smul' := by
      intro r a
      apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
      simp only [map_smul, binarySwapFn_inclusion X A B n, RingHom.id_apply] }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B j
    change HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B j ((HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X A B).d i j (binarySwapFn X A B i c)) =
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B j (binarySwapFn X A B j ((HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X B A).d i j c))
    rw [HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, binarySwapFn_inclusion, binarySwapFn_inclusion,
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_d]

theorem binarySwap_inclusion (n : ℕ) (c : (HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochains X B A).X n) :
    HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((binarySwap X A B).f n c) =
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X B A n c := binarySwapFn_inclusion X A B n c

def unionSwap : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (B ∪ A) ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B) :=
  AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X (fun _ hx => hx.elim Or.inr Or.inl)

theorem unionSwap_inclusion (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (B ∪ A)).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n ((unionSwap X A B).f n c) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (B ∪ A)).f n c :=
  AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient.relativeRationalSubsetCochainMap_inclusion_apply X (fun _ hx => hx.elim Or.inr Or.inl) n c

theorem binarySwap_relative :
    HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X B A ≫ binarySwap X A B =
      unionSwap X A B ≫ HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B n
  change HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n
    ((binarySwap X A B).f n ((HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X B A).f n c)) =
      HodgeConjecture.DegreeTwo.BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n ((HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f n
        ((unionSwap X A B).f n c))
  rw [binarySwap_inclusion, HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion,
    HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion, unionSwap_inclusion]

theorem binarySwap_relative_cohomology (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (B ∪ A) n) :
    HomologicalComplex.homologyMap (binarySwap X A B) n
      (HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X B A) n c) =
      HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) n
        (HomologicalComplex.homologyMap (unionSwap X A B) n c) :=
  ConcreteCategory.congr_hom (by
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun f => HomologicalComplex.homologyMap f n) (binarySwap_relative X A B)) c

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions
