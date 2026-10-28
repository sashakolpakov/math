import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossPoincarePeriodMaps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods

/-! # Period Similitude -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodSimilitude

noncomputable section

/-! A similitude of the actual rational polarization forms gives the
full original polarization pullback equation. The dual is the canonical
Picard pullback map, and the identity is proved as a scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (f : A.abelian.scheme ⟶ B.abelian.scheme) [IsMonHom f] (n : ℕ)

theorem polarization_pullback_of_period_similitude
    (hf : ∀ x y, Intrinsic.ChernPairing.nativePolarizationForm B
      (CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A B f x) (CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A B f y) =
        n • Intrinsic.ChernPairing.nativePolarizationForm A x y) :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom f A.dual B.dual B.polarization = A.polarization.isogeny.hom ^ n := by
  let CA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let DA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
  let DB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)
  let d₀ := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f A.dual B.dual
  let : IsMonHom d₀ := AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.noetherian_nativeDualMap_isMonHom f A.dual B.dual
  let f₀ : CA.toOver ⟶ CB.toOver := f
  let d : DB.toOver ⟶ DA.toOver := d₀
  let : IsMonHom f₀ := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation A) (Polarized.Projectivity.polarizedNativeProjectivePresentation B) f
  let : IsMonHom d := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom B.dual.abelian A.dual.abelian
    (Dual.Projectivity.dualNativeProjectivePresentation B) (Dual.Projectivity.dualNativeProjectivePresentation A) d₀
  have hmaps : f₀ ≫ PeriodIso.nativePolarizationMap B ≫ d = (PeriodIso.nativePolarizationMap A) ^ n := by
    apply PoincarePeriodPairing.nativePoincarePeriodPairing_detects_group_maps A CA
    intro x y
    rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.rationalLift_pow]
    change PoincarePeriodPairing.nativePoincarePeriodPairing A
        (CrossPoincarePeriodMaps.polarizedDualPullbackPeriodMap A B f
          (PeriodIso.nativePolarizationPeriodIso B (CrossPoincarePeriodMaps.polarizedAbelianPeriodMap A B f x))) y =
      PoincarePeriodPairing.nativePoincarePeriodPairing A (n • PeriodIso.nativePolarizationPeriodIso A x) y
    rw [CrossPoincarePeriodMaps.nativePoincarePeriodPairing_cross_map, PoincarePeriodPairing.nativePoincarePeriodPairing_polarization]
    exact (hf x y).trans (by
      rw [map_nsmul, LinearMap.smul_apply, PoincarePeriodPairing.nativePoincarePeriodPairing_polarization])
  have hA : PeriodIso.nativePolarizationMap A = A.polarization.isogeny.hom :=
    Over.OverMorphism.ext (PeriodIso.nativePolarizationMap_left A)
  have hB : PeriodIso.nativePolarizationMap B = B.polarization.isogeny.hom :=
    Over.OverMorphism.ext (PeriodIso.nativePolarizationMap_left B)
  rw [hA, hB] at hmaps
  exact hmaps

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodSimilitude
