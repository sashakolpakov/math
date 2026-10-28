import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenBaseChangePushout
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Base Change Cover -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover.AffineBaseChangeCover

noncomputable section

/-! The actual inverse-image family of an affine cover is an affine cover after scalar base change. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S)
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left) (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom ρ)))

include hp in
theorem affineMorphism : IsAffineHom f :=
  MorphismProperty.of_isPullback hp.flip (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom ρ)))

include hp in
theorem affine (U : X.left.Opens) (hU : IsAffineOpen U) : IsAffineOpen (f ⁻¹ᵁ U) := by
  have : IsAffineHom f := affineMorphism ρ X Y f hp
  exact hU.preimage f

include hp in
theorem separated [IsSeparated X.hom] : IsSeparated Y.hom :=
  MorphismProperty.of_isPullback hp (inferInstance : IsSeparated X.hom)

theorem cover {ι : Type} (U : ι → X.left.Opens) (hU : iSup U = ⊤) :
    (⨆ i, f ⁻¹ᵁ U i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover.AffineBaseChangeCover
