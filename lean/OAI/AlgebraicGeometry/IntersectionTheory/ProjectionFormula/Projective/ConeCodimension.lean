import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Codimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension

/-! # Cone Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeCodimension

noncomputable section

/-! The cone preserves base-support codimension. For a finite
projection of X its codimension is the original cycle-support codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem codimension {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    (Dimension.SpacePresentation.presentation n).supportCodimension (ConeSupport.support L hL η) =
      (Dimension.SpacePresentation.presentation m).supportCodimension (Cone.SmoothPullback.baseSupport η) := by
  have hm := hL.fintype_card_le_finrank
  rw [Fintype.card_fin, LinearFormBasis.dimension] at hm
  have hd := ConeDimension.dimension L hL η
  have hn := Grading.supportDimension_add_codimension (Dimension.SpacePresentation.presentation n) n
    (ConeSupport.support L hL η)
  have hm' := Grading.supportDimension_add_codimension (Dimension.SpacePresentation.presentation m) m
    (Cone.SmoothPullback.baseSupport η)
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ConeSupport.support L hL η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) + _ = n at hn
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Cone.SmoothPullback.baseSupport η) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) + _ = m at hm'
  omega

theorem of_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (W : IrreducibleCloseds X.carrier) :
    (Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension
      (ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W))) =
        X.supportCodimension W := by
  let f : X.toOver ⟶ (Dimension.SpacePresentation.presentation m).toOver :=
    Over.homMk (Projection.FiniteProjective.FromForms.map X m L h) (Projection.FiniteProjective.FromForms.over_base X m L h)
  let : IsFinite f.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  exact (codimension L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W))).trans
    (Finite.Codimension.Projection.image f m W)

theorem intersection_bound (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (W C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ X.embedding ⁻¹'
      (ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W)) :
        Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) : X.supportCodimension W ≤ X.supportCodimension C := by
  let f : X.toOver ⟶ (Dimension.SpacePresentation.presentation m).toOver :=
    Over.homMk (Projection.FiniteProjective.FromForms.map X m L h) (Projection.FiniteProjective.FromForms.over_base X m L h)
  let : IsFinite f.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  apply Finite.Codimension.Projection.preimage f m W C
  rw [ConePreimage.intersection X m L hL h W] at hC
  exact hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeCodimension
