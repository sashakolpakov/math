import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumProductOpenCover
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealPullback
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientOpenCover
import Mathlib.RingTheory.Ideal.Prod

/-! # Product Base Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductBaseCoefficients

noncomputable section

/-! Coefficient ideals on the two factors of a product base combine
into their product ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (A B : CommRingCat.{u}) {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of (A × B)))

theorem ideal_le_iff_product_base (K J : X.IdealSheafData) :
    K ≤ J ↔
      K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.fst A B)))) ≤
        J.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.fst A B)))) ∧
      K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.snd A B)))) ≤
        J.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.snd A B)))) := by
  constructor
  · intro h
    exact ⟨Scheme.IdealSheafData.comap_mono _ h, Scheme.IdealSheafData.comap_mono _ h⟩
  · intro h
    apply Presentations.Ideal.ContainmentOpenLocality.ideal_le_of_openCover ((SpectrumProductOpenCover.spectrumProductOpenCover A B).pullback₁ f)
    intro i
    cases i
    · exact h.1
    · exact h.2

theorem affineIdealCoefficient_product_base (K : X.IdealSheafData) (I : Ideal A) (J : Ideal B)
    (hI : Affine.IdealCoefficientTests.IsAffineIdealCoefficient A
      (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.fst A B))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.fst A B))))) I)
    (hJ : Affine.IdealCoefficientTests.IsAffineIdealCoefficient B
      (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.snd A B))))
      (K.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.snd A B))))) J) :
    Affine.IdealCoefficientTests.IsAffineIdealCoefficient (CommRingCat.of (A × B)) f K (I.prod J) := by
  intro L
  rw [ideal_le_iff_product_base A B f, SpectrumIdealPullback.spectrum_ideal_pullback, SpectrumIdealPullback.spectrum_ideal_pullback]
  erw [hI, hJ]
  have he : (I.prod J).map (RingHom.fst A B) ≤ L.map (RingHom.fst A B) ∧
      (I.prod J).map (RingHom.snd A B) ≤ L.map (RingHom.snd A B) ↔ I.prod J ≤ L :=
    Ideal.idealProdEquiv.le_iff_le
  simpa only [Ideal.map_fst_prod, Ideal.map_snd_prod, CommRingCat.hom_ofHom] using he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ProductBaseCoefficients
