import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CoefficientRefinement
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Refinement Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementPullback.Construction

noncomputable section

/-! The actual polynomial coefficient refinement is a pullback over the coefficient ring. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {H B R : Type u} [CommRing H] [CommRing B] [CommRing R]
  [Algebra H B] [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]

attribute [local instance] Polynomial.algebra

/-- The tensor refinement, before restricting to a retraction
neighborhood, is the actual pullback of the coefficient refinement. -/
theorem etaleLineCoefficientRefinementRing_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B
        (CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[H[X]]
          CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap H B)))
      (Spec.map (CommRingCat.ofHom (algebraMap H R))) := by
  let U := CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing (H := H) (B := B) (R := R)
  have hp : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B B[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap H[X] B[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap H B)))
      (Spec.map (CommRingCat.ofHom (algebraMap H H[X]))) := by
    apply isPullback_SpecMap_of_isPushout
    exact CommRingCat.isPushout_of_isPushout H B H[X] B[X]
  have ht : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B[X] U)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : R →ₐ[H[X]] U).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap H[X] B[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap H[X] R))) := by
    apply isPullback_SpecMap_of_isPushout
    exact CommRingCat.isPushout_tensorProduct H[X] B[X] R
  have h := ht.paste_horiz hp
  have hl : Spec.map (CommRingCat.ofHom (algebraMap B[X] U)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B B[X])) =
      Spec.map (CommRingCat.ofHom (algebraMap B U)) := by
    rw [← Spec.map_comp]
    congr 1
  have hr : Spec.map (CommRingCat.ofHom (algebraMap H[X] R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H H[X])) =
      Spec.map (CommRingCat.ofHom (algebraMap H R)) := by
    rw [← Spec.map_comp]
    congr 1
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq H H[X] R).symm
  rw [hl, hr] at h
  exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementPullback.Construction
