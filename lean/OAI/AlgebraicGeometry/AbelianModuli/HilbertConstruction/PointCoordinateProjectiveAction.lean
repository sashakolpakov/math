import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CoordinateTransform
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateTransformationUniqueness

/-! # Point Coordinate Projective Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointCoordinateProjectiveAction

noncomputable section

/-! Point-coordinate transformations act on the actual
projective scheme, with the transpose convention fixed by the
dual pairing. Frame agreement determines this action uniquely. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

theorem pointCoordinateCoefficientTransform_unit_smul
    (T U : (ι → R) ≃ₗ[R] (ι → R)) (a : Rˣ)
    (h : T.toLinearMap = (a : R) • U.toLinearMap) :
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap =
      (a : R) • (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (Module.evalEquiv R (ι →₀ R)).injective
  apply LinearMap.ext
  intro φ
  change φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T x) = φ ((a : R) • Dual.CoordinateTransform.pointCoordinateCoefficientTransform U x)
  rw [map_smul, Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing, Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing]
  change (Finsupp.llift R R R ι (T ((Finsupp.llift R R R ι).symm φ))) x =
    (a : R) • (Finsupp.llift R R R ι (U ((Finsupp.llift R R R ι).symm φ))) x
  have hv : T ((Finsupp.llift R R R ι).symm φ) =
      (a : R) • U ((Finsupp.llift R R R ι).symm φ) := LinearMap.congr_fun h _
  rw [hv, map_smul]
  rfl

theorem pointCoordinateCoefficientTransform_trans (T U : (ι → R) ≃ₗ[R] (ι → R)) :
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform (T.trans U) =
      (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).trans (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T) := by
  apply LinearEquiv.ext
  intro x
  apply (Module.evalEquiv R (ι →₀ R)).injective
  apply LinearMap.ext
  intro φ
  change φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (T.trans U) x) =
    φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U x))
  rw [Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing, Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing,
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing]
  change (Finsupp.llift R R R ι (U (T ((Finsupp.llift R R R ι).symm φ)))) x =
    (Finsupp.llift R R R ι (U ((Finsupp.llift R R R ι).symm
      (Finsupp.llift R R R ι (T ((Finsupp.llift R R R ι).symm φ)))))) x
  rw [LinearEquiv.symm_apply_apply]

theorem pointCoordinateCoefficientTransform_refl :
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform (LinearEquiv.refl R (ι → R)) = LinearEquiv.refl R (ι →₀ R) := by
  apply LinearEquiv.ext
  intro x
  apply (Module.evalEquiv R (ι →₀ R)).injective
  apply LinearMap.ext
  intro φ
  change φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (LinearEquiv.refl R (ι → R)) x) = φ x
  rw [Dual.CoordinateTransform.pointCoordinateCoefficientTransform_pairing]
  change (Finsupp.llift R R R ι ((Finsupp.llift R R R ι).symm φ)) x = φ x
  rw [LinearEquiv.apply_symm_apply]

variable {n : ℕ}

def pointCoordinateProjectiveIso (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    Projective.ProjectivePresentations.affineProjectiveSpace R n ≅ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm

theorem pointCoordinateProjectiveIso_trans
    (T U : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    (pointCoordinateProjectiveIso (T.trans U)).hom =
      (pointCoordinateProjectiveIso T).hom ≫ (pointCoordinateProjectiveIso U).hom := by
  have h : (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (T.trans U)).symm =
      (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm.trans
        (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm := by
    rw [pointCoordinateCoefficientTransform_trans]
    rfl
  exact (congrArg (fun e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R) =>
    (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom) h).trans
      (Linear.ProjectiveComposition.affineLinearCoordinateIso_trans (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).symm
        (Dual.CoordinateTransform.pointCoordinateCoefficientTransform U).symm)

theorem pointCoordinateProjectiveIso_refl :
    (pointCoordinateProjectiveIso (LinearEquiv.refl R (Fin (n + 1) → R))).hom = 𝟙 _ := by
  apply Over.OverMorphism.ext
  unfold pointCoordinateProjectiveIso
  rw [pointCoordinateCoefficientTransform_refl]
  apply Scalar.LinearProjectiveIdentity.affineLinearCoordinateIso_eq_id_of_inverse_scalar _ (1 : Rˣ)
  simp only [Units.val_one, one_smul]
  rfl

theorem pointCoordinateProjectiveIso_unit_smul
    (T U : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (a : Rˣ)
    (h : T.toLinearMap = (a : R) • U.toLinearMap) :
    (pointCoordinateProjectiveIso T).hom = (pointCoordinateProjectiveIso U).hom :=
  Linear.ProjectiveComposition.affineLinearCoordinateIso_eq_of_inverse_unit_smul _ _ a
    (pointCoordinateCoefficientTransform_unit_smul T U a h)

theorem pointCoordinateProjectiveIso_frame_unique
    {κ : Type*} (v : κ → Fin (n + 1) → R) (σ : Fin (n + 1) → κ) (b : κ)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin (n + 1))) (fun k => v (σ k)) (v b)))
    (T U : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : κ → Rˣ)
    (h : ∀ k, T (v k) = (s k : R) • U (v k)) :
    (pointCoordinateProjectiveIso T).hom = (pointCoordinateProjectiveIso U).hom :=
  pointCoordinateProjectiveIso_unit_smul T U (s b)
    (Frame.CoordinateTransformationUniqueness.configurationFrame_linearEquiv_unique_up_to_unit (Pi.basisFun R (Fin (n + 1))) v σ b hframe T U s h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointCoordinateProjectiveAction
