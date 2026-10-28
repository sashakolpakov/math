import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportDimension

/-! # Proper -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Proper

noncomputable section

/-! The constructed cone meets the embedded smooth scheme
properly, with the exact codimensions used by ThomClass's Tor intersection cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (W : IrreducibleCloseds X.carrier)

def support : (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).DimensionCycleSupport (X.supportCodimension W) :=
  ⟨Projective.ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W)),
    Projective.ConeCodimension.of_projection X m L hL h W⟩

theorem ambient_bound (D : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier)
    (hD : (D : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ⊆
      ((support X m L hL h W).val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ∩ Set.range X.embedding) :
    X.supportCodimension W + (X.ambientDimension - m) ≤
      (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension D := by
  have hr : (D : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ⊆ Set.range X.embedding := fun y hy => (hD hy).2
  let C := Closed.SupportDimension.preimage X.embedding D hr
  have hC : (C : Set X.carrier) ⊆ X.embedding ⁻¹'
      ((support X m L hL h W).val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) := fun x hx => (hD hx).1
  have hb := Projective.ConeCodimension.intersection_bound X m L hL h W C hC
  have he := Closed.SupportDimension.dimension X.embedding D hr (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension)
  rw [X.embedding_over] at he
  have hx := Grading.supportDimension_add_codimension X m C
  have hd := Grading.supportDimension_add_codimension (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
    X.ambientDimension D
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) + _ = X.ambientDimension at hd
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) at he
  have hm := hL.fintype_card_le_finrank
  rw [Fintype.card_fin, LinearFormBasis.dimension] at hm
  omega

theorem pair_meets
    (A : (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).DimensionCycleSupport (X.ambientDimension - m))
    (hA : (A.val : Set (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).carrier) ⊆ Set.range X.embedding) :
    Supports.ProperCycle.pairMeetsProperly (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
      (X.supportCodimension W) (X.ambientDimension - m) (support X m L hL h W) A := by
  intro D hD
  apply ambient_bound X m L hL h W D
  exact fun x hx => ⟨(hD hx).1, hA (hD hx).2⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Proper
