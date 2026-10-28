import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Projectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyHodge

/-! # Period Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso

noncomputable section

/-! The actual polarization isogeny identifies the rational periods of
the original abelian scheme and its now-constructed projective dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IsogenyHodge.AbelianIntrinsicAdapter

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

def nativePolarizationMap :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)).toOver ⟶
      (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)).toOver :=
  Intrinsic.IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap A.abelian A.dual.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (Dual.Projectivity.dualNativeProjectivePresentation A) A.polarization.isogeny

instance nativePolarizationMap_isMonHom : IsMonHom (nativePolarizationMap A) :=
  Intrinsic.IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyMap_isMonHom _ _ _ _ _

theorem nativePolarizationMap_left :
    (nativePolarizationMap A).left = A.polarization.isogeny.hom.left := by
  change 𝟙 _ ≫ A.polarization.isogeny.hom.left ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

def nativePolarizationPeriodIso :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)) :=
  Intrinsic.IsogenyPeriods.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv A.abelian A.dual.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (Dual.Projectivity.dualNativeProjectivePresentation A) A.polarization.isogeny

theorem nativePolarizationPeriodIso_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)))
      (nativePolarizationPeriodIso A).toLinearMap :=
  Intrinsic.IsogenyHodge.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv_isHodgeMap _ _ _ _ _

theorem nativePolarizationPeriodIso_symm_isHodgeMap :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
      (nativePolarizationPeriodIso A).symm.toLinearMap :=
  Intrinsic.IsogenyHodge.AbelianIntrinsicAdapter.nativeIsogenyRationalEquiv_symm_isHodgeMap _ _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso
