import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Iff -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Iff

noncomputable section

/-! Restricting to an integral component preserves the exact native
intersection multiplicities, including all Tor degrees in ThomClass's definition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle

theorem image_point_mem_iff {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
    (A D : IrreducibleCloseds V.carrier) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i D) ∈ (ProperCycleLinearity.imageSupport i A : Set X.carrier) ↔
      CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (A : Set V.carrier) := by
  rw [Cycle.image_point, ProperCycleLinearity.imageSupport_eq_image]
  constructor
  · rintro ⟨y, hy, he⟩
    exact i.left.isOpenEmbedding.injective he ▸ hy
  · intro h
    exact ⟨_, h, rfl⟩

theorem multiplicity_image {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (m : ℕ)
    [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (A B D : IrreducibleCloseds V.carrier) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity V A B D =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (ProperCycleLinearity.imageSupport i A) (ProperCycleLinearity.imageSupport i B)
        (ProperCycleLinearity.imageSupport i D) := by
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (A : Set V.carrier) ∩ (B : Set V.carrier)
  · have hxA := (image_point_mem_iff i A D).mpr h.1
    have hxB := (image_point_mem_iff i B D).mpr h.2
    rw [Truncation.intersectionMultiplicity_eq_relative_sum V m A B D h.1 h.2,
      Truncation.intersectionMultiplicity_eq_relative_sum X m _ _ _ hxA hxB]
    apply Finset.sum_congr rfl
    intro n _
    have ht := Open.SupportTor.localTorLength_eq i.left
      A B (ProperCycleLinearity.imageSupport i A) (ProperCycleLinearity.imageSupport i B)
      (Cycle.image_point i A).symm (Cycle.image_point i B).symm
      (CycleClass.Thom.IntersectionGeometry.supportPoint D) h.1 h.2 (show i.left (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈
        (ProperCycleLinearity.imageSupport i A : Set X.carrier) from by rw [ProperCycleLinearity.imageSupport_eq_image]; exact ⟨_, h.1, rfl⟩)
      (show i.left (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈
        (ProperCycleLinearity.imageSupport i B : Set X.carrier) from by rw [ProperCycleLinearity.imageSupport_eq_image]; exact ⟨_, h.2, rfl⟩) n
    have hp : CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i D) = i.left (CycleClass.Thom.IntersectionGeometry.supportPoint D) :=
      Cycle.image_point i D
    exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ n * (a.toNat : ℚ))
      (ht.trans (Open.SupportTor.localTorLength_congr_point X.carrier _ _ hp.symm _ _ hxA hxB n))
  · have hnot : ¬ CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i D) ∈
        (ProperCycleLinearity.imageSupport i A : Set X.carrier) ∩ (ProperCycleLinearity.imageSupport i B : Set X.carrier) := by
      intro hx
      exact h ⟨(image_point_mem_iff i A D).mp hx.1, (image_point_mem_iff i B D).mp hx.2⟩
    rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right hnot]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Iff
