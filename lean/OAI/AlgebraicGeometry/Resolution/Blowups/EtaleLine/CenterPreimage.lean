import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep

/-! # Center Preimage -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterPreimage.Construction

noncomputable section

/-! Identify actual line-lifted centers with their intrinsic hypersurface preimages. -/

open _root_.Polynomial

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
    [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]

theorem etaleLineCenter_eq_quotient_preimage
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X})) :
    Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (C.map e.toRingHom) =
      C.comap (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X})) := by
  let q := Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X})
  let I := Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (C.map e.toRingHom)
  have hker : RingHom.ker q ≤ I := by
    rw [Ideal.mk_ker]
    exact (Ideal.span_singleton_le_iff_mem I).mpr (Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) (C.map e.toRingHom)).property
  have hm : (I.map q).map e.toRingHom = C.map e.toRingHom := by
    rw [Ideal.map_map]
    exact RetractionStep.Construction.etaleLineRetraction_center e (C.map e.toRingHom)
  have heq : I.map q = C := by
    have h := congrArg (Ideal.comap e.toRingHom) hm
    rwa [Ideal.comap_map_of_bijective e.toRingHom e.bijective,
      Ideal.comap_map_of_bijective e.toRingHom e.bijective] at h
  have hrec := Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective I
  rw [heq, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hrec
  exact hrec.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterPreimage.Construction
