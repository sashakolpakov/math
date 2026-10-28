import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Cycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Moving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DimensionDrop

/-! # Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Moving

noncomputable section

/-! Every target cycle can be moved into a position where the native
smooth projection formula holds against a prescribed source support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem representatives {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
    (m n p q s : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hd : q + n = s + m) (a : Y.RationalDimensionCycle p) (W : X.DimensionCycleSupport q) :
    ∃ a' : Y.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (Cycle.flatMap f p a') (Finsupp.single W 1) ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly Y p s a' (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1)) ∧
      ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
        (Supports.ProperCycle.intersectionBilinear X m p q (Cycle.flatMap f p a') (Finsupp.single W 1)) =
        Supports.ProperCycle.intersectionBilinear Y n p s a' (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1)) := by
  by_cases hi : Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) = s
  · have hdim := Grading.image_dimension_eq_of_grade f m n q s hd W hi
    obtain ⟨a', ha, hp, hA, U, _, hU, hgood⟩ := Finite.Moving.Projection.representatives f m n p q a W hdim
    let : Etale (U.ι ≫ Support.Map.supportImageMap f W.val) := hU
    let B : Y.DimensionCycleSupport s := ⟨ProperCycleLinearity.imageSupport f W.val, hi⟩
    rw [hi] at hA hgood
    have hY : ∀ A ∈ a'.support, Supports.ProperCycle.pairMeetsProperly Y p s A B := hA
    refine ⟨a', ha, hp, ?_, ?_⟩
    · exact ProjectionFormula.Etale.Cycles.Projection.meets f p q s a' W B rfl hY
    · exact ProjectionFormula.Etale.Cycles.Projection.cycle f m n p q s hd a' W B rfl hp hY U hgood
  · have hdx := Grading.supportDimension_add_codimension X m W.val
    have hdy := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f W.val)
    have hle := Support.Fields.image_dimension_le f W.val
    rw [W.property] at hdx
    have hdrop : s < Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) := by omega
    obtain ⟨a', ha, hA, hrel⟩ := Relative.Moving.with_images f m n p q a (Finsupp.single W 1)
    have hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (Cycle.flatMap f p a') (Finsupp.single W 1) := by
      intro L hL D hD C hC
      obtain ⟨A, hAs, _, hLA⟩ := CycleSupport.origin f m n p a' L hL
      exact hrel A hAs D hD C (fun x hx => ⟨(hC hx).2, hLA (hC hx).1⟩)
    have hAW : ∀ A ∈ a'.support, ∀ C : IrreducibleCloseds Y.carrier,
        (C : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f W.val →
          p + Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) ≤ Y.supportCodimension C :=
      fun A hAs => hA A hAs W (by simp)
    refine ⟨a', ha, hp, ?_, DimensionDrop.Projection.cycle f m n p q s a' W hp hAW hdrop⟩
    rw [DimensionDrop.Projection.support_zero f q s W hdrop]
    intro A _ B hB
    simp at hB

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Moving
