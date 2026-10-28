import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupCochain
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BinarySmallRightCup

/-! # Support Cup Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupLift.Constructions

noncomputable section

section

/-!
# Genuine union-relative cup representatives with a controlled correction

The correction vanishes on both individual complements. It is obtained from
equality in the actual small-quotient cohomology, including degree zero.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
variable {p q : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
variable (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q)

theorem twoSupportCup_exists_small_primitive :
    ∃ (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (p+q))
      (v : ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc (p+q)).X₁),
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q) u =
        SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b) ∧
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).sc (p+q)).f v =
        (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f (p+q) u.val -
          SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B a.val b.val := by
  obtain ⟨u,hu⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (p+q)
    (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b))
  have he := SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class X A B hA hB a b
  rw [← hu, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality] at he
  obtain ⟨v,hv⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q)
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q) u)
    (SupportCupCochain.Constructions.twoSupportSmallCupCocycle X A B a b)).mp he
  exact ⟨u,v,hu,hv⟩

theorem twoSupportCup_exists_relative_representative :
    ∃ (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (p+q))
      (v : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc (p+q)).X₁),
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q) u =
        SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ q b) ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f ((ComplexShape.up ℕ).prev (p+q)) v = 0 ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f ((ComplexShape.up ℕ).prev (p+q)) v = 0 ∧
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc (p+q)).f v =
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (p+q) u.val -
          AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a.val)
            ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b.val) := by
  obtain ⟨u,v,hu,hv⟩ := twoSupportCup_exists_small_primitive X A B hA hB a b
  let w := BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B ((ComplexShape.up ℕ).prev (p+q)) v
  refine ⟨u,w,hu,?_,?_,?_⟩
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B A
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) _ v
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B B
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) _ v
  · have he := congrArg (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q)) hv
    change BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q)
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).d ((ComplexShape.up ℕ).prev (p+q)) (p+q) v) = _ at he
    rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, map_sub, BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion,
      SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion] at he
    exact he

end

/-! The correction to a positive-degree supported cup lies in the explicit preceding degree. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem twoSupportCup_exists_relative_representative_succ
    (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) (q+1)) :
    ∃ (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (p+q+1))
      (v : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X (p+q)),
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q+1) u =
        SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p (q+1) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (q+1) b) ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f (p+q) v = 0 ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f (p+q) v = 0 ∧
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (p+q) (p+q+1) v =
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (p+q+1) u.val -
          AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a.val)
            ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f (q+1) b.val) := by
  obtain ⟨u,hu⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (p+q+1)
    (SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p (q+1) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a) (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (q+1) b))
  have he := SupportCupCochain.Constructions.twoSupportCohomologyCup_smallCochain_class X A B hA hB a b
  rw [← hu] at he
  change HomologicalComplex.homologyMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q+1)
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q+1) u) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (p+q+1) (SupportCupCochain.Constructions.twoSupportSmallCupCocycle X A B (p := p) (q := q+1) a b) at he
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality] at he
  obtain ⟨v,hv⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ (BinarySmallCochains.Constructions.binarySmallCochains X A B) (p+q)
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B) (p+q+1) u)
    (SupportCupCochain.Constructions.twoSupportSmallCupCocycle X A B (p := p) (q := q+1) a b)).mp he
  refine ⟨u,BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q) v,hu,?_,?_,?_⟩
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B A
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) (p+q) v
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B B
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) (p+q) v
  · have h := congrArg (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1)) hv
    change BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1)
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).d (p+q) (p+q+1) v) =
      BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1)
        ((BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f (p+q+1) u.val -
          SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B (p := p) (q := q+1) a.val b.val) at h
    rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, map_sub, BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion] at h
    have hi : BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B (p+q+1) (SupportCupCochain.Constructions.twoSupportSmallCupCochain X A B (p := p) (q := q+1) a.val b.val) =
        AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p a.val)
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f (q+1) b.val) :=
      SupportCupCochain.Constructions.twoSupportSmallCupCochain_inclusion X A B (p := p) (q := q+1) a.val b.val
    rw [hi] at h
    exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupLift.Constructions
