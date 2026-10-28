import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovedProperPosition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IndependentTupleOrbit
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CoordinateChange

/-! # Moving Position -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovingPosition

noncomputable section

section

/-! The properly positioned cone is an actual projective linear
translate of any original cone with the same auxiliary base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace MovedOrbit

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData.Projection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)
  (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
    ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)

theorem target_eq (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)
    (he : Projective.ConeSupport.coordinates (BlockData.Projection.targetForms X m L) = LinearFormBasis.GradedMap.gradedHom e.toLinearMap) :
    BlockData.Projection.targetProjection X m L hT = LinearFormAutomorphism.map e := by
  have hf : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)).map (Projective.ConeSupport.coordinates (BlockData.Projection.targetForms X m L)) := by
    rw [he]
    exact LinearFormAutomorphism.irrelevant_le e
  change Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates (BlockData.Projection.targetForms X m L))
    (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) _ = _
  rw [GlobalProjective.Projection.restriction _ hf, Category.id_comp]
  simp only [he, LinearFormAutomorphism.map]

theorem exists_translation (hLI : LinearIndependent ℂ (BlockData.Projection.sourceForms X m L))
    (hLT : LinearIndependent ℂ (BlockData.Projection.targetForms X m L))
    (L₀ : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (h₀ : LinearIndependent ℂ L₀)
    (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier) :
    ∃ e : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      LinearFormAutomorphism.map e '' (Projective.ConeSupport.support L₀ h₀ (CycleClass.Thom.IntersectionGeometry.supportPoint S) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) =
        (MovedConeSupport.cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
  obtain ⟨eT, heT⟩ := SquareIso.Projection.exists_equiv (BlockData.Projection.targetForms X m L) hLT
  let M := LinearTupleMap.precompose (BlockData.Projection.sourceForms X m L) eT.symm
  have hM : LinearIndependent ℂ M := LinearTupleMap.precompose_independent (BlockData.Projection.sourceForms X m L) hLI eT.symm
  obtain ⟨e, he⟩ := IndependentTupleOrbit.exists_automorphism L₀ M h₀ hM
  refine ⟨e.symm, (CoordinateChange.source_image L₀ M h₀ hM e he (CycleClass.Thom.IntersectionGeometry.supportPoint S)).trans ?_⟩
  have hp := CoordinateChange.target_change (BlockData.Projection.sourceForms X m L) hLI eT (CycleClass.Thom.IntersectionGeometry.supportPoint S)
  rw [← target_eq X m L hT eT heT] at hp
  exact congrArg (fun x : Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension =>
    (irreducibleSetEquivPoints.symm x : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) hp.symm

end MovedOrbit

end

/-! An actual projective linear translate of the original cone meets
the source and every prescribed support in the expected codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_translation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (L₀ : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (h₀ : LinearIndependent ℂ L₀)
    (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) :
    ∃ e : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      (∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ X.embedding ⁻¹'
          (LinearFormAutomorphism.map e ''
            (Projective.ConeSupport.support L₀ h₀ (CycleClass.Thom.IntersectionGeometry.supportPoint S) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) →
        (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S ≤ X.supportCodimension C) ∧
      ∀ t, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆ X.embedding ⁻¹'
          (LinearFormAutomorphism.map e ''
            (Projective.ConeSupport.support L₀ h₀ (CycleClass.Thom.IntersectionGeometry.supportPoint S) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) ∩
              (Z t : Set X.carrier) →
        (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S + X.supportCodimension (Z t) ≤
          X.supportCodimension C := by
  obtain ⟨L, _, hT, hLI, hLT, _, hX, hZ⟩ := MovedProperPosition.MovingChoice.exists_coordinates X m S Z
  obtain ⟨e, he⟩ := MovedOrbit.exists_translation X m L hT hLI hLT L₀ h₀ S
  refine ⟨e, ?_, ?_⟩
  · intro C hC
    rw [he] at hC
    exact hX C hC
  · intro t C hC
    rw [he] at hC
    exact hZ t C hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovingPosition
