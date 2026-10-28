import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearTupleMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConePreimage

/-! # Coordinate Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CoordinateChange

noncomputable section

/-! Cone formation commutes with invertible changes of source and
target linear coordinates, at the level of actual homogeneous prime ideals. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearTupleMap

theorem image_ideal {n : ℕ} (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    (LinearFormAutomorphism.map e x).asHomogeneousIdeal.toIdeal =
      x.asHomogeneousIdeal.toIdeal.map (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap).toRingHom := by
  change x.asHomogeneousIdeal.toIdeal.comap (LinearFormAutomorphism.algebraEquiv e).toRingEquiv.toRingHom = _
  exact (Ideal.map_symm (LinearFormAutomorphism.algebraEquiv e).toRingEquiv).symm

theorem target_change {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)
    (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    Projective.ConeSupport.genericPoint L hL (LinearFormAutomorphism.map e η) =
      Projective.ConeSupport.genericPoint (LinearTupleMap.precompose L e.symm) (LinearTupleMap.precompose_independent L hL e.symm) η := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  change (LinearFormAutomorphism.map e η).asHomogeneousIdeal.toIdeal.map (Projective.ConeSupport.coordinates L).toRingHom =
    η.asHomogeneousIdeal.toIdeal.map (Projective.ConeSupport.coordinates (LinearTupleMap.precompose L e.symm)).toRingHom
  rw [image_ideal, Ideal.map_map, LinearTupleMap.precompose_coordinates]
  rfl

theorem source_change {m n : ℕ} (L M : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (hM : LinearIndependent ℂ M)
    (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (he : ∀ a, e (L a) = M a)
    (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    LinearFormAutomorphism.map e.symm (Projective.ConeSupport.genericPoint L hL η) = Projective.ConeSupport.genericPoint M hM η := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  rw [image_ideal]
  change (η.asHomogeneousIdeal.toIdeal.map (Projective.ConeSupport.coordinates L).toRingHom).map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap).toRingHom =
    η.asHomogeneousIdeal.toIdeal.map (Projective.ConeSupport.coordinates M).toRingHom
  have hM' : M = fun a => e (L a) := funext (fun a => (he a).symm)
  rw [Ideal.map_map, hM', LinearTupleMap.postcompose_coordinates]
  rfl

theorem source_image {m n : ℕ} (L M : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (hM : LinearIndependent ℂ M)
    (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (he : ∀ a, e (L a) = M a)
    (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    LinearFormAutomorphism.map e.symm '' (Projective.ConeSupport.support L hL η : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) =
      (Projective.ConeSupport.support M hM η : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  let : IsIso (LinearFormAutomorphism.map e.symm) :=
    inferInstanceAs (IsIso (LinearFormAutomorphism.iso e.symm).hom)
  have h := Projective.ConePreimage.finite_image (LinearFormAutomorphism.map e.symm) (Projective.ConeSupport.support L hL η)
  change (irreducibleSetEquivPoints.symm (LinearFormAutomorphism.map e.symm
    (irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm (Projective.ConeSupport.genericPoint L hL η)))) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = _ at h
  rw [irreducibleSetEquivPoints.apply_symm_apply, source_change L M hL hM e he η] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CoordinateChange
