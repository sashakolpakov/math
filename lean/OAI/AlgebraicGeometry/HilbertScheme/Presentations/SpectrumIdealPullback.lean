import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealCoordinates

/-! # Spectrum Ideal Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealPullback

noncomputable section

/-! Extended base ideals agree on the two sides of an affine base-change square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem spectrum_ideal_pullback {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (φ : R ⟶ A) (L : Ideal R) :
    (((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f).comap (pullback.fst f (Spec.map φ)) =
      ((SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map φ.hom)).comap
        (pullback.snd f (Spec.map φ)) := by
  have hb : ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap (Spec.map φ) =
      (SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map φ.hom) := by
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates A).injective
    rw [SpectrumIdealCoordinates.spectrumIdealCoordinates_comap, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
  rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
    Scheme.IdealSheafData.comap_comp, hb]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealPullback
