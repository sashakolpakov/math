import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps

/-! # Cross Poincare Period Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossPoincarePeriodMaps

noncomputable section

/-! The canonical dual of an arbitrary original abelian group map is
adjoint for the actual Poincare period pairings. The comparison uses
the original normalized Poincare line bundles and native homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (f : A.abelian.scheme ⟶ B.abelian.scheme) [IsMonHom f]

def polarizedAbelianPeriodMap :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) →ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)) :=
  Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (Polarized.Projectivity.polarizedNativeProjectivePresentation B) f

def polarizedDualPullbackPeriodMap :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)) →ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)) := by
  let : IsMonHom (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f A.dual B.dual) :=
    AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.noetherian_nativeDualMap_isMonHom f A.dual B.dual
  exact Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodMap B.dual.abelian A.dual.abelian
    (Dual.Projectivity.dualNativeProjectivePresentation B) (Dual.Projectivity.dualNativeProjectivePresentation A)
    (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f A.dual B.dual)

theorem nativePoincarePeriodPairing_cross_map
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)))
    (w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    PoincarePeriodPairing.nativePoincarePeriodPairing A (polarizedDualPullbackPeriodMap A B f v) w =
      PoincarePeriodPairing.nativePoincarePeriodPairing B v (polarizedAbelianPeriodMap A B f w) := by
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
  have hA := Product.ClassPairingNaturality.nativeProductClassPairing_pullback DB CA DA CA d (𝟙 CA.toOver)
    (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DB v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w)
  have hB := Product.ClassPairingNaturality.nativeProductClassPairing_pullback DB CA DB CB (𝟙 DB.toOver) f₀
    (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DB v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w)
  rw [Product.ClassPairingNaturality.nativePointHomology_id] at hA hB
  have hd := AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare.Construction.noetherian_nativeDualMap_poincare A.dual B.dual f
  change Product.ClassPairingNaturality.nativeProductClassPairing DA CA (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DA (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d v)) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w) =
    Product.ClassPairingNaturality.nativeProductClassPairing DB CB (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DB v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CB (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f₀ w))
  rw [Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality d v, Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f₀ w]
  exact hA.symm.trans ((congrArg (fun c => Product.ClassPairingNaturality.nativeProductClassPairing DB CA c
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DB v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w)) hd).trans hB)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossPoincarePeriodMaps
