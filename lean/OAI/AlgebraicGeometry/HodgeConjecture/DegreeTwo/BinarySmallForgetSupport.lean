import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRelativeComparison
import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup

/-! # Binary Small Forget Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallForgetSupport.Constructions

noncomputable section

/-! Forget one vanishing condition through the actual quotient maps on integral chains. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B S : Set X)
variable (g : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X S ⟶ CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B)

def binarySmallCochainToRelativeMap :
    BinarySmallCochains.Constructions.binarySmallCochains X A B ⟶ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X S where
  f n := ModuleCat.ofHom {
    toFun := fun c => (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S n).symm (c.comp (g.f n).hom)
    map_add' := by intros; simp only [LinearMap.add_comp, map_add]
    map_smul' := by intros; simp only [LinearMap.smul_comp, map_smul, RingHom.id_apply] }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S j).injective
    ext z
    change (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S j)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X S).d i j
        ((AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S i).symm (c.comp (g.f i).hom))) z =
      (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S j)
        ((AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S j).symm
          ((c.comp ((CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).d j i).hom).comp (g.f j).hom)) z
    rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact congrArg c (ConcreteCategory.congr_hom (g.comm j i) z).symm

variable (hg : CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X S ≫ g = CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)

include hg in
theorem binarySmallCochainToRelativeMap_inclusion (n : ℕ) (c : (BinarySmallCochains.Constructions.binarySmallCochains X A B).X n) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).f n
      ((binarySmallCochainToRelativeMap X A B S g).f n c) = BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n c := by
  apply (BinarySmallCochains.Constructions.rationalSingularIntegralDualEquiv X n).injective
  ext z
  rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_eval]
  change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).f n
      ((binarySmallCochainToRelativeMap X A B S g).f n c)) z = _
  rw [← AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection]
  change (AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S n)
    ((AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X S n).symm (c.comp (g.f n).hom))
      ((CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X S).f n z) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg c (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hg n) z)

include hg in
theorem binarySmallRelativeCochainMap_forget (hS : S ⊆ A ∪ B) :
    BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B ≫ binarySmallCochainToRelativeMap X A B S g =
      AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X hS := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of ℚ ℚ) X S n
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X S).f n
    ((binarySmallCochainToRelativeMap X A B S g).f n ((BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f n c)) = _
  rw [binarySmallCochainToRelativeMap_inclusion X A B S g hg,
    BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion, AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient.relativeRationalSubsetCochainMap_inclusion_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallForgetSupport.Constructions
