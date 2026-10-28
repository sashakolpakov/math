import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportBoundaryRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupLift

/-! # Cup Connecting Component -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CupConnectingComponent.Constructions

noncomputable section

/-! Lift one connecting component of a degree-two supported cup, retaining both vanishings. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem cochainRestriction_zero_of_subset (X : TopCat.{0}) {A J : Set X} (h : A ⊆ J)
    (n : ℕ) (w : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (hw : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X J).f n w = 0) :
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n w = 0 := by
  have hr : w ∈ LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X J).f n).hom := by
    rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
    exact hw
  obtain ⟨v,rfl⟩ := hr
  rw [← AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient.relativeRationalSubsetCochainMap_inclusion_apply X h n v]
  exact SupportBoundaryRepresentatives.Constructions.relativeCochainInclusion_restriction_apply X A n _

theorem relativeDegreeTwoCup_d (X : TopCat.{0}) (C : Set X) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (2+q) (2+q+1)
      (AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val) b) =
    AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1) b) := by
  have ha : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d 2 3
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val) = 0 :=
    AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero _ 2 3
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C) 2 a)
  change (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)).d (2+q) (2+q+1)
    (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ)
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val) b) = _
  rw [AlgebraicTopology.Products.Cup.cupWith_coboundary, ha, AlgebraicTopology.Products.Cup.cupWith_zero_left, map_zero, zero_add]
  norm_num
  rfl

theorem degreeTwoCup_connecting_component
    (X : TopCat.{0}) (C A J : Set X) (hC : IsOpen C) (hA : IsOpen A) (hAJ : A ⊆ J) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X q)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X J) (q+1))
    (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C ∪ J)) (2+q+1))
    (z : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X (2+q))
    (hd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d q (q+1)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f q b) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X J).f (q+1) c.val)
    (hzC : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X C).f (2+q) z = 0)
    (hzJ : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X J).f (2+q) z = 0)
    (hz : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (2+q) (2+q+1) z =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C ∪ J)).f (2+q+1) u.val -
        AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val)
          ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X J).f (q+1) c.val)) :
    ∃ (v : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C ∪ A)).X (2+q))
      (t : ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc (2+q)).X₁),
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C ∪ A)).d (2+q) (2+q+1) v =
        (AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X (Set.union_subset_union_right C hAJ)).f (2+q+1) u.val ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X C).f ((ComplexShape.up ℕ).prev (2+q)) t = 0 ∧
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f ((ComplexShape.up ℕ).prev (2+q)) t = 0 ∧
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).sc (2+q)).f t =
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C ∪ A)).f (2+q) v -
          (AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val)
            ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f q b) + z) := by
  let w := AlgebraicTopology.Products.Cup.singularCup X ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f q b) + z
  let uA := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X
    (Set.union_subset_union_right C hAJ)) (2+q+1) u
  have hwC : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X C).f (2+q) w = 0 := by
    dsimp only [w]
    rw [map_add, hzC, add_zero]
    exact CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_restriction_zero X C
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) a.val ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f q b)
  have hwA : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f (2+q) w = 0 := by
    dsimp only [w]
    rw [map_add, cochainRestriction_zero_of_subset X hAJ (2+q) z hzJ, add_zero]
    exact CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_restriction_zero X A
      (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
      (LinearMap.mul ℚ ℚ) ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X C).f 2 a.val) b
  have hw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d (2+q) (2+q+1) w =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C ∪ A)).f (2+q+1) uA.val := by
    dsimp only [w]
    rw [map_add, relativeDegreeTwoCup_d, hd, hz]
    change _ = (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C ∪ A)).f (2+q+1)
      ((AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X (Set.union_subset_union_right C hAJ)).f (2+q+1) u.val)
    rw [AlgebraicTopology.Duality.Poincare.SupportConnectingAmbient.relativeRationalSubsetCochainMap_inclusion_apply]
    abel
  exact SeparateSupportPrimitive.Constructions.relative_primitive_from_separate_vanishing X C A hC hA (2+q) uA w hwC hwA hw

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CupConnectingComponent.Constructions
