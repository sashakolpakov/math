import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

/-! # Exact Polarization Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactPolarizationPairing

noncomputable section

/-! The actual lambda-Poincare pairing itself recovers the original
polarization form. Antisymmetrization introduces no change of scale. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarizationHomologyPairing_eq_original :
    Polarization.HomologyForm.polarizationHomologyPairing A =
      HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
        (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
        (Intrinsic.ChernClasses.lineBundleChernClass (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).variety.presentation
          (Intrinsic.ChernPairing.polarizationLineBundle A)) := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  obtain ⟨e⟩ := Polarization.Biextension.polarizationLineBundle_poincare A
  have h := BiextensionPeriodPairing.nativeBiextensionHomologyPairing_eq B (Intrinsic.ChernPairing.polarizationLineBundle A) (Polarization.Biextension.polarizationOriginalBiextension A) e
  have hc := congrArg (Product.ClassPairingNaturality.nativeProductClassPairing B B) (Polarization.Biextension.polarizationOriginalBiextension_class A)
  exact hc.symm.trans h

theorem polarizationHomologyPairing_antisymm
    (x y : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme)) :
    Polarization.HomologyForm.polarizationHomologyPairing A x y = -Polarization.HomologyForm.polarizationHomologyPairing A y x := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let c := Intrinsic.ChernClasses.lineBundleChernClass B.variety.presentation (Intrinsic.ChernPairing.polarizationLineBundle A)
  have he := polarizationHomologyPairing_eq_original A
  exact (LinearMap.congr_fun (LinearMap.congr_fun he x) y).trans
    ((HomologyPairingAntisymmetry.homologyClassPairing_antisymm B c x y).trans
      (congrArg Neg.neg (LinearMap.congr_fun (LinearMap.congr_fun he y) x)).symm)

theorem nativePolarizationForm_eq_poincare_exact :
    Intrinsic.ChernPairing.nativePolarizationForm A = (Polarization.HomologyForm.polarizationHomologyPairing A).compl₁₂
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).toLinearMap
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).toLinearMap := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let b : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme) →ₗ[ℚ]
    HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme) →ₗ[ℚ] ℚ := Polarization.HomologyForm.polarizationHomologyPairing A
  have hb : (1 / 2 : ℚ) • (b - b.flip) = b := by
    ext x y
    change (1 / 2 : ℚ) * (b x y - b y x) = b x y
    have hyx : b y x = -b x y := polarizationHomologyPairing_antisymm A y x
    rw [hyx]
    ring
  exact (Polarization.HomologyForm.nativePolarizationForm_eq_poincare A).trans
    (congrArg (fun F => F.compl₁₂ (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).toLinearMap
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).toLinearMap) hb)

theorem polarizationHomologyPairing_separating
    (x : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme))
    (hx : ∀ y, Polarization.HomologyForm.polarizationHomologyPairing A x y = 0) : x = 0 := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let e := Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B
  have hz : e.symm x = 0 := by
    apply Intrinsic.ChernPeriod.nativePolarizationForm_separating A
    intro y
    have he := LinearMap.congr_fun (LinearMap.congr_fun (nativePolarizationForm_eq_poincare_exact A) (e.symm x)) y
    exact he.trans ((congrArg (fun z => Polarization.HomologyForm.polarizationHomologyPairing A z (e y)) (e.apply_symm_apply x)).trans (hx (e y)))
  exact e.symm.injective (hz.trans e.symm.map_zero.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactPolarizationPairing
