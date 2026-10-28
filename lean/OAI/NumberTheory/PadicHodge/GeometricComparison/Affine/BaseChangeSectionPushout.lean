import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OverSpec
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Base Change Section Pushout -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeSectionPushout.AffineBaseChangeSectionPushout

noncomputable section

/-! Global sections on an actual affine scalar-base-change square form the native coefficient-ring pushout. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S)
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) [IsAffine X.left]
  (h : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom ρ)))

include h in
theorem affine : IsAffine Y.left := IsAffine.of_isPullback h

include h in
theorem isPushout :
    IsPushout (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap R X ⊤))
      (CommRingCat.ofHom (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S Y ⊤)) f.appTop := by
  let eR := Scheme.ΓSpecIso (CommRingCat.of R)
  let eS := Scheme.ΓSpecIso (CommRingCat.of S)
  apply (isPushout_appTop_of_isPullback h).flip.of_iso eR eS (Iso.refl _) (Iso.refl _)
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ)
  · rw [OverSpec.AffineOverSpec.coefficient_map, Iso.refl_hom, Category.comp_id,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · rw [OverSpec.AffineOverSpec.coefficient_map, Iso.refl_hom, Category.comp_id,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeSectionPushout.AffineBaseChangeSectionPushout
