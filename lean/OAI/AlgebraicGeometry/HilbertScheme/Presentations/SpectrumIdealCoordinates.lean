import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IdealFunctoriality

/-! # Spectrum Ideal Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealCoordinates

noncomputable section

/-! Actual ideal sheaves on an affine spectrum have their ordinary ring
ideals as coordinates, naturally for both image and inverse image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def spectrumIdealCoordinates (R : CommRingCat.{u}) :
    (Spec R).IdealSheafData ≃o Ideal R :=
  (Scheme.IdealSheafData.equivOfIsAffine (X := Spec R)).toOrderIso.trans
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.idealComapOrderIso

theorem spectrumIdealCoordinates_map {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (I : (Spec A).IdealSheafData) :
    spectrumIdealCoordinates R (I.map (Spec.map φ)) =
      (spectrumIdealCoordinates A I).comap φ.hom := by
  change (Scheme.IdealSheafData.equivOfIsAffine (I.map (Spec.map φ))).comap
    (Scheme.ΓSpecIso R).inv.hom =
      ((Scheme.IdealSheafData.equivOfIsAffine I).comap (Scheme.ΓSpecIso A).inv.hom).comap φ.hom
  rw [AbelianModuli.HilbertConstruction.Affine.IdealFunctoriality.affine_ideal_map, Ideal.comap_comap, Ideal.comap_comap]
  have he : (Spec.map φ).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom =
      (Scheme.ΓSpecIso A).inv.hom.comp φ.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality φ).symm
  rw [he]

theorem spectrumIdealCoordinates_comap {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (I : (Spec R).IdealSheafData) :
    spectrumIdealCoordinates A (I.comap (Spec.map φ)) =
      (spectrumIdealCoordinates R I).map φ.hom := by
  let ER := spectrumIdealCoordinates R
  let EA := spectrumIdealCoordinates A
  have hiff (J : (Spec A).IdealSheafData) :
      EA (I.comap (Spec.map φ)) ≤ EA J ↔ (ER I).map φ.hom ≤ EA J := by
    rw [EA.le_iff_le, ← Scheme.IdealSheafData.le_map_iff_comap_le,
      Ideal.map_le_iff_le_comap, ← spectrumIdealCoordinates_map φ J]
    exact ER.le_iff_le.symm
  apply le_antisymm
  · have h := (hiff (EA.symm ((ER I).map φ.hom))).mpr
      (EA.apply_symm_apply _).symm.le
    exact h.trans_eq (EA.apply_symm_apply _)
  · exact (hiff (I.comap (Spec.map φ))).mp le_rfl

theorem spectrumIdealCoordinates_kernel {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    spectrumIdealCoordinates R (Spec.map φ).ker = RingHom.ker φ.hom := by
  rw [← Scheme.IdealSheafData.map_bot, spectrumIdealCoordinates_map, OrderIso.map_bot]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealCoordinates
