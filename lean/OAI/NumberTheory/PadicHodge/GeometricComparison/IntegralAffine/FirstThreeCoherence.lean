import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCoordinateForms

/-! # First Three Coherence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeCoherence.IntegralAffineFirstThreeCoherence

noncomputable section

/-! The actual first three form modules on affine schemes are quasicoherent and finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormModules.IntegralAffineFormModules

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

theorem localization_transport
    (P : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat A)
    (n : ℕ) (hn : n ≤ 2) (a : A)
    (e : P ≅ Affine.FormsCech.CoordinateForms.specPresheaf R A n) :
    IsLocalizedModule (Submonoid.powers a)
      (P.map (PrimeSpectrum.basicOpen a).leTop.op).hom := by
  let := IntegralFirst.ThreeCoordinateForms.IntegralFirstThreeCoordinateForms.specPresheaf_isLocalized R A n hn a
  exact PresheafLocalization.PresheafLocalizationTransport.isLocalized e
    (PrimeSpectrum.basicOpen a).leTop.op (Submonoid.powers a)

theorem localized (n : ℕ) (hn : n ≤ 2) (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((FormModules.IntegralAffineFormModules.scalars R A n).map (PrimeSpectrum.basicOpen a).leTop.op).hom :=
  localization_transport R A (FormModules.IntegralAffineFormModules.scalars R A n) n hn a (FormModules.IntegralAffineFormModules.iso R A n)

theorem quasicoherent (n : ℕ) (hn : n ≤ 2) :
    (Integral.FormsModules.IntegralFormsModules.sheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).IsQuasicoherent :=
  IntegralComparison.Affine.LocalizingModule.quasicoherent A
    (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) (localized R A n hn)

theorem finiteType [Algebra.FiniteType R A] (n : ℕ) (hn : n ≤ 2) :
    (Integral.FormsModules.IntegralFormsModules.sheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n).IsFiniteType := by
  let : Module.Finite A ((IntegralComparison.Affine.LocalizingModule.scalars A
      (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).obj (op ⊤)) :=
    FormCoherence.IntegralAffineFormCoherence.finite_top R A n
  exact IntegralComparison.Affine.LocalizingModule.finiteType A
    (Integral.FormsModules.IntegralFormsModules.presheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) (localized R A n hn)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeCoherence.IntegralAffineFirstThreeCoherence
