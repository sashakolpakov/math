import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CochainPrescribedLift
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupLift

/-! # Separate Support Primitive -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SeparateSupportPrimitive.Constructions

noncomputable section

/-! A primitive vanishing on each of two opens lifts to their genuine union-relative complex. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)

theorem binarySmallCochainLift_prescribed_d (n : ℕ)
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n+1))
    (w : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hwA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n w = 0)
    (hwB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n w = 0)
    (hw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1) w =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) u.val) :
    (BinarySmallCochains.Constructions.binarySmallCochains X A B).d n (n+1) (BinarySmallCochains.Constructions.binarySmallCochainLift X A B n w hwA hwB) =
      (BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap X A B).f (n+1) u.val := by
  apply BinarySmallCochains.Constructions.binarySmallCochainInclusion_injective X A B (n+1)
  rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion,
    BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion]
  exact hw

include hA hB in
theorem relative_primitive_from_separate_vanishing (n : ℕ)
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n+1))
    (w : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hwA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n w = 0)
    (hwB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n w = 0)
    (hw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1) w =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) u.val) :
    ∃ (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).X n)
      (z : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc n).X₁),
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)).d n (n+1) v = u.val ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f ((ComplexShape.up ℕ).prev n) z = 0 ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f ((ComplexShape.up ℕ).prev n) z = 0 ∧
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc n).f z =
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n v - w := by
  let w₀ := BinarySmallCochains.Constructions.binarySmallCochainLift X A B n w hwA hwB
  obtain ⟨v,z,hv,hz⟩ := CochainPrescribedLift.Constructions.binarySmallRelative_prescribed_lift X A B hA hB n u w₀
    (binarySmallCochainLift_prescribed_d X A B n u w hwA hwB hw)
  let z₀ := BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B ((ComplexShape.up ℕ).prev n) z
  refine ⟨v,z₀,hv,?_,?_,?_⟩
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B A
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_left X A B) _ z
  · exact BinarySmallRightCup.Constructions.binarySmallCochainInclusion_restriction X A B B
      (CycleClass.Geometric.HomologyWithSupports.Cycles.subspaceChainInclusion_binarySmallComplement_right X A B) _ z
  · have he := congrArg (BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n) hz
    change BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n
      ((BinarySmallCochains.Constructions.binarySmallCochains X A B).d ((ComplexShape.up ℕ).prev n) n z) = _ at he
    rw [BinarySmallCochains.Constructions.binarySmallCochainInclusion_d, map_sub, BinarySmallRelativeComparison.Constructions.binarySmallRelativeCochainMap_inclusion] at he
    change ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc n).f z₀ =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f n v -
        BinarySmallCochains.Constructions.binarySmallCochainInclusion X A B n (BinarySmallCochains.Constructions.binarySmallCochainLift X A B n w hwA hwB) at he
    rw [BinarySmallCochains.Constructions.binarySmallCochainLift_inclusion] at he
    exact he

include hA hB in
theorem relative_class_zero_of_separate_primitive (n : ℕ)
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (A ∪ B)) (n+1))
    (w : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hwA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n w = 0)
    (hwB : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X B).f n w = 0)
    (hw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n+1) w =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B)).f (n+1) u.val) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n+1) u = 0 := by
  obtain ⟨v,z,hv,-,-,-⟩ := relative_primitive_from_separate_vanishing X A B hA hB n u w hwA hwB hw
  exact (CochainPrescribedLift.Constructions.cochainClass_succ_eq_zero_iff _ n u).mpr ⟨v,hv⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SeparateSupportPrimitive.Constructions
