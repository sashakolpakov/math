import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests

/-! # Quotient Coefficient Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientCoefficientLift

noncomputable section

/-! Coefficient ideals on a quotient base give the least base ideal
among ideals containing that quotient's kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem ideal_comap_le_iff_closed {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsClosedImmersion j] (I J : Y.IdealSheafData) (hJ : j.ker ≤ J) :
    I.comap j ≤ J.comap j ↔ I ≤ J := by
  constructor
  · intro h
    have he := Scheme.IdealSheafData.le_map_iff_comap_le.mpr h
    rwa [Closed.ImmersionIdealEmbedding.ideal_map_comap_closed j J hJ] at he
  · exact fun h => Scheme.IdealSheafData.comap_mono j h

theorem affine_quotient_coefficient_lift {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (K : X.IdealSheafData) (φ : R ⟶ A)
    (hφ : Function.Surjective φ) (C : Ideal A)
    (hC : IdealCoefficientTests.IsAffineIdealCoefficient A (pullback.snd f (Spec.map φ))
      (K.comap (pullback.fst f (Spec.map φ))) C) :
    RingHom.ker φ.hom ≤ C.comap φ.hom ∧
      ∀ L : Ideal R, RingHom.ker φ.hom ≤ L →
        (K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f ↔ C.comap φ.hom ≤ L) := by
  let g := Spec.map φ
  let p := pullback.fst f g
  let q := pullback.snd f g
  let : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective φ hφ
  refine ⟨fun r hr => by change φ r ∈ C; rw [show φ r = 0 from hr]; exact C.zero_mem, ?_⟩
  intro L hL
  have hbase : ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap g =
      (SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map φ.hom) := by
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates A).injective
    rw [SpectrumIdealCoordinates.spectrumIdealCoordinates_comap, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
  have hker : p.ker ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    apply Scheme.IdealSheafData.comap_mono f
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates R).le_iff_le.mp
    rw [SpectrumIdealCoordinates.spectrumIdealCoordinates_kernel, OrderIso.apply_symm_apply]
    exact hL
  have hpull : (((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm L).comap f).comap p =
      ((SpectrumIdealCoordinates.spectrumIdealCoordinates A).symm (L.map φ.hom)).comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp, hbase]
  have he := ideal_comap_le_iff_closed p K _ hker
  rw [hpull, hC] at he
  refine he.symm.trans ⟨?_, ?_⟩
  · intro hc
    have hm := Ideal.comap_mono (f := φ.hom) hc
    rw [Ideal.comap_map_of_surjective φ.hom hφ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hL] at hm
    exact hm
  · intro hc
    have hm := Ideal.map_mono (f := φ.hom) hc
    rw [Ideal.map_comap_of_surjective φ.hom hφ] at hm
    exact hm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.QuotientCoefficientLift
