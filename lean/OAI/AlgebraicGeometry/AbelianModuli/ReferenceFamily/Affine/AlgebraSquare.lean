import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality

/-! # Algebra Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraSquare

noncomputable section

/-! A literal square of affine algebra equivalences gives the
corresponding square of their original affine scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R P P' T T' : Type) [CommRing R] [CommRing P] [CommRing P'] [CommRing T] [CommRing T']
    [Algebra R P] [Algebra R P'] [Algebra R T] [Algebra R T']

theorem affineAlgIso_hom_left (e : P ≃ₐ[R] T) :
    (EtaleSplittingAt.EtaleSplitting.affineAlgIso R P e).hom.left = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

theorem affineAlgebraEquiv_square (e : P ≃ₐ[R] T) (e' : P' ≃ₐ[R] T')
    (q : P →ₐ[R] P') (r : T →ₐ[R] T') (h : e'.toAlgHom.comp q = r.comp e.toAlgHom) :
    AlgebraAutomorphismNaturality.affineOverAlgHom R T T' r ≫ (EtaleSplittingAt.EtaleSplitting.affineAlgIso R P e).hom =
      (EtaleSplittingAt.EtaleSplitting.affineAlgIso R P' e').hom ≫ AlgebraAutomorphismNaturality.affineOverAlgHom R P P' q := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom r.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) =
    Spec.map (CommRingCat.ofHom e'.toRingHom) ≫ Spec.map (CommRingCat.ofHom q.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a => (AlgHom.congr_fun h a).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraSquare
