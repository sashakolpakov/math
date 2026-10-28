import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport

/-! # Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Moving

noncomputable section

/-! Relative moving controls both images and inverse images. For a
smooth morphism this gives properly meeting native pullback cycles. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n in
theorem with_images (p q : ℕ) (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ a' : Y.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a' ∧
      (∀ A ∈ a'.support, ∀ B ∈ b.support, ∀ D : IrreducibleCloseds Y.carrier,
        (D : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f B.val →
          p + Y.supportCodimension (ProperCycleLinearity.imageSupport f B.val) ≤ Y.supportCodimension D) ∧
      (∀ A ∈ a'.support, ∀ B ∈ b.support, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ (B.val : Set X.carrier) ∩ f.left ⁻¹' (A.val : Set Y.carrier) →
          p + q ≤ X.supportCodimension C) := by
  choose F hmem hproper using (fun B : b.support => ProperMoving.family f m n B.val.val)
  let T := Finset.univ.biUnion F
  obtain ⟨a', ha, hp⟩ := General.ChowMoving.cycle Y n (fun Z : T => Z.val) p a
  have hP (A : Y.DimensionCycleSupport p) (hA : A ∈ a'.support) (B : b.support) :
      ProperMoving.ProperAgainst Y p A (F B) := by
    intro Z hZ D hD
    exact hp ⟨Z, Finset.mem_biUnion.mpr ⟨B, Finset.mem_univ _, hZ⟩⟩ A hA D hD
  refine ⟨a', ha, ?_, ?_⟩
  · intro A hA B hB D hD
    exact hP A hA ⟨B, hB⟩ (ProperCycleLinearity.imageSupport f B.val) (hmem ⟨B, hB⟩) D hD
  · intro A hA B hB C hC
    have he := hproper ⟨B, hB⟩ p A (hP A hA ⟨B, hB⟩) C hC
    rw [B.property] at he
    omega

include m n in
theorem smooth [Smooth f.left] (p q : ℕ)
    (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ∃ a' : Y.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (ProjectionFormula.Smooth.Cycle.flatMap f p a') b := by
  obtain ⟨a', ha, hp⟩ := ProperMoving.cycle f m n p q a b
  refine ⟨a', ha, ?_⟩
  intro A hA B hB C hC
  obtain ⟨D, hD, _, hAD⟩ := ProjectionFormula.Smooth.CycleSupport.origin f m n p a' A hA
  exact hp D hD B hB C (fun x hx => ⟨(hC hx).2, hAD (hC hx).1⟩)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Moving
