import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleLinearExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Moving

/-! # Dimension Drop -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DimensionDrop

noncomputable section

/-! Properly positioned intersections on a support whose image has
larger codimension contribute zero to graded projection pushforward. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  (m n p q s : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  (a : Y.RationalDimensionCycle p) (W : X.DimensionCycleSupport q)
  (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (Cycle.flatMap f p a) (Finsupp.single W 1))
  (hA : ∀ A ∈ a.support, ∀ C : IrreducibleCloseds Y.carrier,
    (C : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f W.val →
      p + Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) ≤ Y.supportCodimension C)
  (hdrop : s < Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val))

include n hp hA hdrop in
theorem zero : ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
    (Supports.ProperCycle.intersectionBilinear X m p q (Cycle.flatMap f p a) (Finsupp.single W 1)) = 0 := by
  rw [ProperCycleLinearity.cyclePushforward, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro E hE
  obtain ⟨L, hL, D, hD, he⟩ := CycleLinearExpansion.support X m p q
    (Cycle.flatMap f p a) (Finsupp.single W 1) E hE
  have hDW : D = W := by simpa using hD
  subst D
  obtain ⟨A, hAs, _, hLA⟩ := CycleSupport.origin f m n p a L hL
  have hn := Finsupp.mem_support_iff.mp he
  rw [Supports.ProperCycle.pairCycle_apply X m p q L W (hp L hL W (by simp))] at hn
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint E.val ∈ (L.val : Set X.carrier) ∩ W.val := by
    by_contra h
    exact hn (dite_eq_right h)
  have hsub := (Supports.supportPoint_mem_iff_subset
    (⟨(L.val : Set X.carrier) ∩ W.val, L.val.isClosed.inter W.val.isClosed⟩ : Closeds X.carrier) E.val).mp hx
  have hIm : (ProperCycleLinearity.imageSupport f E.val : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f W.val := by
    rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hLA (hsub hx).1, ⟨x, (hsub hx).2, rfl⟩⟩
  have hh := hA A hAs (ProperCycleLinearity.imageSupport f E.val) hIm
  have hgrade : Y.supportCodimension (ProperCycleLinearity.imageSupport f E.val) ≠ p + s := by omega
  simp only [ProperCycleLinearity.cyclePushforwardGenerator, CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right hgrade, smul_zero]

include hdrop in
omit [Smooth f.left] [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap] in
theorem support_zero : ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1) = 0 := by
  rw [ProperCycleLinearity.cyclePushforward_single]
  simp only [ProperCycleLinearity.cyclePushforwardGenerator, CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right (Nat.ne_of_gt hdrop), smul_zero]

include hp hA hdrop in
theorem cycle : ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
    (Supports.ProperCycle.intersectionBilinear X m p q (Cycle.flatMap f p a) (Finsupp.single W 1)) =
    Supports.ProperCycle.intersectionBilinear Y n p s a (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1)) := by
  rw [zero f m n p q s a W hp hA hdrop, support_zero f q s W hdrop, map_zero]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DimensionDrop
