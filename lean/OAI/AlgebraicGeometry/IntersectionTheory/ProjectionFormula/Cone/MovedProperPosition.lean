import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedConeSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProjectedSupport

/-! # Moved Proper Position -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovedProperPosition

noncomputable section

section

/-! The incidence bound on the disjoint blocks makes the new cone
meet every prescribed source support in the expected codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)
  (hS : ∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal)
  (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
    ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)
  (hLI : LinearIndependent ℂ (BlockData.Projection.sourceForms X m L))
  (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier)
  (Z : IrreducibleCloseds X.carrier)

def projected : Closeds (Projective.BlockSupports.ambient X m).carrier :=
  ProjectedSupport.intersection (Projective.BlockSupports.ambient X m) m L
    (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z)
    (MovedConeSupport.target_no_base X m L hT S) (MovedConeSupport.source_no_base X m L hS Z)

theorem mem_projected (x : X.carrier) (hxZ : x ∈ (Z : Set X.carrier))
    (hxC : X.embedding x ∈ (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) :
    (Projective.BlockSupports.source X m).left x ∈ projected X m L hS hT S Z := by
  have hproj : BlockData.Projection.sourceProjection X m L hS x ∈ BlockData.Projection.targetProjection X m L hT ''
      (S : Set (Projective.Dimension.SpacePresentation.presentation m).carrier) :=
    Eq.mp (congrArg (fun T : Set X.carrier => x ∈ T) (MovedConeSupport.preimage X m L hS hT hLI S)) hxC
  obtain ⟨s, hs, he⟩ := hproj
  let A := ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S
  let B := ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z
  have hA : (Projective.BlockSupports.target X m).left s ∈ (A : Set (Projective.BlockSupports.ambient X m).carrier) := by
    rw [ProperCycleLinearity.imageSupport_eq_image]
    exact ⟨s, hs, rfl⟩
  have hB : (Projective.BlockSupports.source X m).left x ∈ (B : Set (Projective.BlockSupports.ambient X m).carrier) := by
    rw [ProperCycleLinearity.imageSupport_eq_image]
    exact ⟨x, hxZ, rfl⟩
  refine ⟨CycleClass.Thom.IntersectionGeometry.supportPreimage B ((Projective.BlockSupports.source X m).left x) hB,
    ⟨CycleClass.Thom.IntersectionGeometry.supportPreimage A ((Projective.BlockSupports.target X m).left s) hA, ?_⟩, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec B ((Projective.BlockSupports.source X m).left x) hB⟩
  exact (BlockSupport.Projection.target_point X m L hT A
    (MovedConeSupport.target_no_base X m L hT S) s hA).trans
    (he.trans (BlockSupport.Projection.source_point X m L hS B
      (MovedConeSupport.source_no_base X m L hS Z) x hB).symm)

include hS in
theorem dimension_bound
    (hI : Projection.Generic.InductionBounds.incidence (Projective.BlockSupports.ambient X m)
      (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z) L)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ X.embedding ⁻¹'
      (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ∩ (Z : Set X.carrier)) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + m ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension S (Projective.Dimension.SpacePresentation.presentation m).structureMap +
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap := by
  have hi : (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) C : Set (Projective.BlockSupports.ambient X m).carrier) ⊆ projected X m L hS hT S Z := by
    rw [ProperCycleLinearity.imageSupport_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    exact mem_projected X m L hS hT hLI S Z x (hC hx).2 (hC hx).1
  have hb := ProjectedSupport.dimension_bound (Projective.BlockSupports.ambient X m) m L
    (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z)
    (MovedConeSupport.target_no_base X m L hT S) (MovedConeSupport.source_no_base X m L hS Z)
    (Projective.BlockSupports.disjoint X m Z S).symm hI (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) C) hi
  rw [Projective.BlockSupports.source_dimension, Projective.BlockSupports.target_dimension, Projective.BlockSupports.source_dimension] at hb
  exact hb

include hS in
theorem codimension_bound [SmoothOfRelativeDimension m X.structureMap]
    (hI : Projection.Generic.InductionBounds.incidence (Projective.BlockSupports.ambient X m)
      (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z) L)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ X.embedding ⁻¹'
      (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ∩ (Z : Set X.carrier)) :
    (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S + X.supportCodimension Z ≤
      X.supportCodimension C := by
  have hb := dimension_bound X m L hS hT hLI S Z hI C hC
  have hc := Grading.supportDimension_add_codimension X m C
  have hz := Grading.supportDimension_add_codimension X m Z
  have hs := Grading.supportDimension_add_codimension (Projective.Dimension.SpacePresentation.presentation m) m S
  omega

end

/-! There is an actual cone of the prescribed base codimension
whose intersection with the source meets every prescribed support properly.
The independent coordinates on both blocks are retained for the moving family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace MovingChoice

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData.Projection

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)
      (_hS : ∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal)
      (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
        ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)
      (hLI : LinearIndependent ℂ (BlockData.Projection.sourceForms X m L)),
      LinearIndependent ℂ (BlockData.Projection.targetForms X m L) ∧
      (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension
        (MovedConeSupport.cone X m L hT hLI S) =
          (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S ∧
      (∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ X.embedding ⁻¹'
          (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) →
        (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S ≤ X.supportCodimension C) ∧
      ∀ t, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ X.embedding ⁻¹'
          (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) ∩ (Z t : Set X.carrier) →
        (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S + X.supportCodimension (Z t) ≤
          X.supportCodimension C := by
  let H : Unit ⊕ τ → IrreducibleCloseds X.carrier := Sum.elim (fun _ => Integral.Fundamental.whole X) Z
  obtain ⟨L, hS, hT, hLI, hLT, hI⟩ := DisjointBlockForms.Projection.exists_forms X m S H
  refine ⟨L, hS, hT, hLI, hLT, MovedConeSupport.codimension X m L hT hLI S, ?_, ?_⟩
  · intro C hC
    have hb := codimension_bound X m L hS hT hLI S (Integral.Fundamental.whole X)
      (hI (Sum.inl ())) C (fun x hx => ⟨hC hx, trivial⟩)
    rw [Integral.Fundamental.whole_codimension X m, add_zero] at hb
    exact hb
  · intro t C hC
    exact codimension_bound X m L hS hT hLI S (Z t) (hI (Sum.inr t)) C hC

end MovingChoice

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovedProperPosition
