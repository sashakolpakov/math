import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SerreIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentSerre
import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction

/-! # Support Classes -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.SupportClasses.Constructions

noncomputable section

/-! The native Serre pair cycle maps to the actual cup for every
proper pair of supports on an arbitrary smooth projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions.Mixed OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.IntersectionBettiBilinear
open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem same_component_pair_class (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (B : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) q)
    (h : Proper.Intersection.pairMeetsProperly X p q ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩)
      ((X.componentDimensionSupportEquiv q).symm ⟨C, B⟩)) :
    X.geometricCycleClassMap (p + q)
      (Proper.Intersection.pairCycle X p q ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩)
        ((X.componentDimensionSupportEquiv q).symm ⟨C, B⟩)) =
    ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear X p q
      (X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩) 1))
      (X.geometricCycleClassMap q (Finsupp.single ((X.componentDimensionSupportEquiv q).symm ⟨C, B⟩) 1)) := by
  apply X.componentBetti_ext (ModuleCat.of ℚ ℚ) ((p + q) + (p + q))
  intro D
  rw [ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear_restrict, ← X.componentBettiEquiv_apply,
    X.componentBettiEquiv_geometricCycleClassMap]
  by_cases he : C = D
  · subst D
    rw [ComponentSerre.Constructions.pairCycle_restrict_same X C p q A B h, ComponentRestriction.Constructions.Class.geometricClass_single_component_same,
      ComponentRestriction.Constructions.Class.geometricClass_single_component_same, one_smul, one_smul, ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear_apply]
    exact Integral.SerreIntersection.Constructions.geometricClass_supportedSerreCycle (X.componentVariety C) p q A B
      (ComponentSerre.Constructions.component_pair_proper X C p q A B h)
  · rw [ComponentSerre.Constructions.pairCycle_restrict_other X C p q A B h D he, map_zero,
      ComponentRestriction.Constructions.Class.geometricClass_single_component_ne X p C D A 1 he, map_zero, LinearMap.zero_apply]

theorem pair_cycle_class (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (h : Proper.Intersection.pairMeetsProperly X p q A B) :
    X.geometricCycleClassMap (p + q) (Proper.Intersection.pairCycle X p q A B) =
      ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear X p q (X.geometricCycleClassMap p (Finsupp.single A 1))
        (X.geometricCycleClassMap q (Finsupp.single B 1)) := by
  obtain ⟨⟨C, A⟩, rfl⟩ := (X.componentDimensionSupportEquiv p).symm.surjective A
  obtain ⟨⟨D, B⟩, rfl⟩ := (X.componentDimensionSupportEquiv q).symm.surjective B
  by_cases he : C = D
  · subst D
    exact same_component_pair_class X C p q A B h
  · rw [ComponentSerre.Constructions.Mixed.pairCycle_mixed_zero X C D p q A B he h, map_zero]
    apply X.componentBetti_ext (ModuleCat.of ℚ ℚ) ((p + q) + (p + q))
    intro E
    rw [map_zero, ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear_restrict]
    by_cases hCE : C = E
    · subst E
      rw [ComponentRestriction.Constructions.Class.geometricClass_single_component_ne X q D C B 1 (Ne.symm he), map_zero]
    · rw [ComponentRestriction.Constructions.Class.geometricClass_single_component_ne X p C E A 1 hCE, map_zero, LinearMap.zero_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.SupportClasses.Constructions
