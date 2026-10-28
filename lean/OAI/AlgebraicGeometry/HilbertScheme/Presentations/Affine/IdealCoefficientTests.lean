import OAI.AlgebraicGeometry.HilbertScheme.Presentations.KernelFlatBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SpectrumIdealCoordinates

/-! # Ideal Coefficient Tests -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests

noncomputable section

/-! A least base ideal containing an ideal on a flat source detects
vanishing after every affine base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (f : X ⟶ Spec R)
variable (K : X.IdealSheafData) (I : Ideal R)

def IsAffineIdealCoefficient : Prop :=
  ∀ J : Ideal R, K ≤ ((SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm J).comap f ↔ I ≤ J

theorem affineIdealCoefficient_unique {J : Ideal R}
    (hI : IsAffineIdealCoefficient R f K I) (hJ : IsAffineIdealCoefficient R f K J) : I = J := by
  exact le_antisymm ((hI J).mp ((hJ J).mpr le_rfl))
    ((hJ I).mp ((hI I).mpr le_rfl))

theorem affineIdealCoefficient_test [Flat f] (hI : IsAffineIdealCoefficient R f K I)
    {A : CommRingCat.{u}} (φ : R ⟶ A) :
    K.comap (pullback.fst f (Spec.map φ)) = ⊥ ↔ I ≤ RingHom.ker φ.hom := by
  rw [KernelFlatBaseChange.ideal_vanishing_flat_baseChange]
  have hk : (Spec.map φ).ker = (SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm (RingHom.ker φ.hom) := by
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates R).injective
    rw [OrderIso.apply_symm_apply, SpectrumIdealCoordinates.spectrumIdealCoordinates_kernel]
  rw [hk]
  exact hI _

theorem affineIdealCoefficient_of_tests [Flat f]
    (hI : ∀ (A : CommRingCat.{u}) (φ : R ⟶ A),
      K.comap (pullback.fst f (Spec.map φ)) = ⊥ ↔ I ≤ RingHom.ker φ.hom) :
    IsAffineIdealCoefficient R f K I := by
  intro J
  let φ : R ⟶ CommRingCat.of (R ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have h := hI _ φ
  rw [KernelFlatBaseChange.ideal_vanishing_flat_baseChange] at h
  have hk : (Spec.map φ).ker = (SpectrumIdealCoordinates.spectrumIdealCoordinates R).symm J := by
    apply (SpectrumIdealCoordinates.spectrumIdealCoordinates R).injective
    rw [OrderIso.apply_symm_apply, SpectrumIdealCoordinates.spectrumIdealCoordinates_kernel]
    exact Ideal.mk_ker
  rw [hk] at h
  simpa only [φ, CommRingCat.hom_ofHom, Ideal.mk_ker] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests
