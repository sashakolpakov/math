import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTor

/-! # Component Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComponentIntersection

noncomputable section

/-! Restricting to an integral component preserves the exact native
intersection multiplicities, including all Tor degrees in ThomClass's definition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Constructions

theorem image_point_mem_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (A D : IrreducibleCloseds (X.componentVariety C).carrier) :
    IntersectionGeometry.supportPoint (X.componentSupportImage C D) ∈ (X.componentSupportImage C A : Set X.carrier) ↔
      IntersectionGeometry.supportPoint D ∈ (A : Set (X.componentVariety C).carrier) := by
  rw [show IntersectionGeometry.supportPoint (X.componentSupportImage C D) = X.componentInclusion C (IntersectionGeometry.supportPoint D)
    from X.componentSupportImage_genericPoint C D]
  change X.componentInclusion C (IntersectionGeometry.supportPoint D) ∈
    X.componentInclusion C '' (A : Set (X.componentVariety C).carrier) ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    have he' := (X.componentInclusion C).isOpenEmbedding.injective he
    exact he' ▸ hy
  · intro h
    exact ⟨_, h, rfl⟩

theorem multiplicity_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (A B D : IrreducibleCloseds (X.componentVariety C).carrier) :
    IntersectionGeometry.intersectionMultiplicity (X.componentVariety C).presentation A B D =
      IntersectionGeometry.intersectionMultiplicity X (X.componentSupportImage C A) (X.componentSupportImage C B)
        (X.componentSupportImage C D) := by
  let V := (X.componentVariety C).presentation
  by_cases h : IntersectionGeometry.supportPoint D ∈ (A : Set V.carrier) ∩ (B : Set V.carrier)
  · have hxA := (image_point_mem_iff X C A D).mpr h.1
    have hxB := (image_point_mem_iff X C B D).mpr h.2
    rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_left h, IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
    apply Finset.sum_congr rfl
    intro n _
    have ht := Open.SupportTor.Constructions.localTorLength_eq (X.componentInclusion C)
      A B (X.componentSupportImage C A) (X.componentSupportImage C B)
      (X.componentSupportImage_genericPoint C A).symm (X.componentSupportImage_genericPoint C B).symm
      (IntersectionGeometry.supportPoint D) h.1 h.2 (show X.componentInclusion C (IntersectionGeometry.supportPoint D) ∈
        (X.componentSupportImage C A : Set X.carrier) from ⟨_, h.1, rfl⟩)
      (show X.componentInclusion C (IntersectionGeometry.supportPoint D) ∈
        (X.componentSupportImage C B : Set X.carrier) from ⟨_, h.2, rfl⟩) n
    have hp : IntersectionGeometry.supportPoint (X.componentSupportImage C D) = X.componentInclusion C (IntersectionGeometry.supportPoint D) :=
      X.componentSupportImage_genericPoint C D
    exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ n * (a.toNat : ℚ))
      (ht.trans (Open.SupportTor.Constructions.localTorLength_congr_point X.carrier _ _ hp.symm _ _ hxA hxB n))
  · have hnot : ¬ IntersectionGeometry.supportPoint (X.componentSupportImage C D) ∈
        (X.componentSupportImage C A : Set X.carrier) ∩ (X.componentSupportImage C B : Set X.carrier) := by
      intro hx
      exact h ⟨(image_point_mem_iff X C A D).mp hx.1, (image_point_mem_iff X C B D).mp hx.2⟩
    rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, IntersectionGeometry.intersectionMultiplicity, dite_eq_right hnot]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComponentIntersection
