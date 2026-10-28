import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Iff -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Iff

noncomputable section

/-! Restricting to an integral component preserves the exact native
intersection multiplicities, including all Tor degrees in ThomClass's definition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem image_point_mem_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (A D : IrreducibleCloseds (X.componentVariety C).carrier) :
    CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) ∈ (X.componentSupportImage C A : Set X.carrier) ↔
      CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (A : Set (X.componentVariety C).carrier) := by
  rw [show CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) = X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint D)
    from X.componentSupportImage_genericPoint C D]
  change X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈
    X.componentInclusion C '' (A : Set (X.componentVariety C).carrier) ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    have he' := (X.componentInclusion C).isOpenEmbedding.injective he
    exact he' ▸ hy
  · intro h
    exact ⟨_, h, rfl⟩

theorem multiplicity_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier)
    (A B D : IrreducibleCloseds (X.componentVariety C).carrier) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (X.componentVariety C).presentation A B D =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (X.componentSupportImage C A) (X.componentSupportImage C B)
        (X.componentSupportImage C D) := by
  let V := (X.componentVariety C).presentation
  let : SmoothOfRelativeDimension m V.structureMap := Image.component_relativeDimension X m C
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (A : Set V.carrier) ∩ (B : Set V.carrier)
  · have hxA := (image_point_mem_iff X C A D).mpr h.1
    have hxB := (image_point_mem_iff X C B D).mpr h.2
    rw [Truncation.intersectionMultiplicity_eq_relative_sum V m A B D h.1 h.2,
      Truncation.intersectionMultiplicity_eq_relative_sum X m _ _ _ hxA hxB]
    apply Finset.sum_congr rfl
    intro n _
    have ht := Open.SupportTor.localTorLength_eq (X.componentInclusion C)
      A B (X.componentSupportImage C A) (X.componentSupportImage C B)
      (X.componentSupportImage_genericPoint C A).symm (X.componentSupportImage_genericPoint C B).symm
      (CycleClass.Thom.IntersectionGeometry.supportPoint D) h.1 h.2 (show X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈
        (X.componentSupportImage C A : Set X.carrier) from ⟨_, h.1, rfl⟩)
      (show X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint D) ∈
        (X.componentSupportImage C B : Set X.carrier) from ⟨_, h.2, rfl⟩) n
    have hp : CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) = X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint D) :=
      X.componentSupportImage_genericPoint C D
    exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ n * (a.toNat : ℚ))
      (ht.trans (Open.SupportTor.localTorLength_congr_point X.carrier _ _ hp.symm _ _ hxA hxB n))
  · have hnot : ¬ CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) ∈
        (X.componentSupportImage C A : Set X.carrier) ∩ (X.componentSupportImage C B : Set X.carrier) := by
      intro hx
      exact h ⟨(image_point_mem_iff X C A D).mp hx.1, (image_point_mem_iff X C B D).mp hx.2⟩
    rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right hnot]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Iff
