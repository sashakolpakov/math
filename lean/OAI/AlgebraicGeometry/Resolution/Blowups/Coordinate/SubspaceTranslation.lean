import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceIdeal

/-! # Subspace Translation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslation.Construction

noncomputable section

/-! Translation along the free coordinates preserves the defining ideal of a coordinate subspace. -/

open _root_.MvPolynomial

theorem polynomialCoordinateProjection_ker_comap_translation
    {σ τ R : Type*} [CommRing R] (a : τ → R) :
    (RingHom.ker (SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := σ) (τ := τ) (R := R)).toRingHom).comap
      (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a)).toRingHom =
      RingHom.ker SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom := by
  ext p
  change SubspaceIdeal.Construction.polynomialCoordinateProjection (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a) p) = 0 ↔
    SubspaceIdeal.Construction.polynomialCoordinateProjection p = 0
  have h := DFunLike.congr_fun (SubspaceIdeal.Construction.polynomialCoordinateProjection_translation (σ := σ) a) p
  change SubspaceIdeal.Construction.polynomialCoordinateProjection (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a) p) =
    PolynomialTranslation.Construction.polynomialTranslate a (SubspaceIdeal.Construction.polynomialCoordinateProjection p) at h
  rw [h]
  exact (PolynomialTranslation.Construction.polynomialTranslationEquiv a).map_eq_zero_iff

theorem polynomialCoordinateProjection_ker_map_translation
    {σ τ R : Type*} [CommRing R] (a : τ → R) :
    (RingHom.ker (SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := σ) (τ := τ) (R := R)).toRingHom).map
      (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a)).toRingHom =
      RingHom.ker SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom := by
  let q := SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := σ) (τ := τ) (R := R)
  let t := PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ : σ => 0) a)
  calc
    (RingHom.ker q.toRingHom).map t.toRingHom =
        ((RingHom.ker q.toRingHom).comap t.toRingHom).map t.toRingHom :=
      congrArg (Ideal.map t.toRingHom) (polynomialCoordinateProjection_ker_comap_translation a).symm
    _ = RingHom.ker q.toRingHom := Ideal.map_comap_of_surjective _
      (PolynomialTranslation.Construction.polynomialTranslationEquiv (Sum.elim (fun _ : σ => 0) a)).surjective _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslation.Construction
