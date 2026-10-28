import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters

/-! # Laurent Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LaurentNaturality.Construction

noncomputable section

/-!
# CartierDuality: integral Laurent coordinates of characters
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- An integral Laurent-algebra homomorphism is determined by the image
of its invertible generator. -/
theorem integralLaurentHom_ext {B : Type u} [CommRing B]
    {f g : Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ) →+* B}
    (h : f (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1)) =
      g (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1))) : f = g := by
  apply MonoidAlgebra.ringHom_ext'
  · apply RingHom.ext
    intro z
    have hi : (f.comp MonoidAlgebra.singleOneRingHom).comp
        ULift.ringEquiv.symm.toRingHom =
      (g.comp MonoidAlgebra.singleOneRingHom).comp ULift.ringEquiv.symm.toRingHom :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun hi z.down
  · exact MonoidHom.ext_mint h

variable (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- A group-like element defines a character with values in the
integral multiplicative group, by extending the Laurent coefficients. -/
def integralCharacterMap (z : GroupLike R A) :
    Characters.Construction.MultiplicativeGroupCoordinate (ULift.{u} ℤ) →+* A :=
  (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom.toRingHom.comp
    (MonoidAlgebra.mapRingHom (Multiplicative ℤ)
      ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom))

@[simp]
theorem integralCharacterMap_generator (z : GroupLike R A) :
    integralCharacterMap R A z (MonoidAlgebra.of _ _ (Multiplicative.ofAdd 1)) = z.val := by
  simp [integralCharacterMap, MonoidAlgebra.of_apply]
  exact Characters.Construction.groupLikeEquivHopfCharacters_generator R A z

/-- The scheme character corresponding to a group-like element is the
spectrum of the associated Laurent-algebra homomorphism. -/
theorem groupLikeEquivSchemeCharacters_left (z : GroupLike R A) :
    (Characters.Construction.groupLikeEquivSchemeCharacters R A z).hom.hom.left =
      Spec.map (CommRingCat.ofHom (Characters.Construction.groupLikeEquivHopfCharacters R A z).toAlgHom.toRingHom) :=
  rfl

/-- Integral character coordinates commute with every ring map that
carries the defining group-like element to the target element. -/
theorem integralCharacterMap_natural
    (S B : Type u) [CommRing S] [CommRing B] [HopfAlgebra S B]
    (z : GroupLike R A) (w : GroupLike S B) (f : A →+* B)
    (h : f z.val = w.val) :
    f.comp (integralCharacterMap R A z) = integralCharacterMap S B w := by
  apply integralLaurentHom_ext
  simpa only [RingHom.comp_apply, integralCharacterMap_generator] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LaurentNaturality.Construction
