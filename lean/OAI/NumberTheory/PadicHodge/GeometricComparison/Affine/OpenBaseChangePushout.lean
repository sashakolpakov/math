import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeSectionPushout
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Open Base Change Pushout -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenBaseChangePushout.AffineOpenBaseChangePushout

noncomputable section

/-! On an actual affine open and its base-change preimage, the original section rings form the native scalar pushout. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

theorem coefficient_map (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens) :
    CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ U le_top := rfl

variable {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S)
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) (h : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom ρ)))

include h in
theorem isPushout (U : X.left.Opens) (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X U))
      (CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y (f ⁻¹ᵁ U))) (f.app U) := by
  have hV : f ⁻¹ᵁ U = f ⁻¹ᵁ U ⊓ Y.hom ⁻¹ᵁ ⊤ := by simp
  have hi := isIso_pushoutSection_of_isAffineOpen h (US := ⊤) (UT := ⊤) (UX := U) (UY := f ⁻¹ᵁ U)
    le_top le_top hV (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := f ⁻¹ᵁ U)
    le_top le_top hV).mp hi
  apply hp.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Scheme.ΓSpecIso (CommRingCat.of S))
    (Iso.refl _) (Iso.refl _)
  · have ht : (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom ρ)).appTop :=
      OverSpec.AffineOverSpec.appLE_top R (Over.mk (Spec.map (CommRingCat.ofHom ρ)))
    exact (congrArg (fun a => a ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom) ht).trans
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))
  · rw [coefficient_map, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  · rw [coefficient_map, Iso.refl_hom, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      (f.app_eq_appLE (U := U)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenBaseChangePushout.AffineOpenBaseChangePushout
