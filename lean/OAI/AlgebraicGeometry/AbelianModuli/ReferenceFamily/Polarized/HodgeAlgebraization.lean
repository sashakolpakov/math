import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso

/-! # Hodge Algebraization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization

noncomputable section

/-! Algebraization of an integral Hodge isomorphism preserving the
actual polarization form also preserves the actual polarization
isogeny and the normalized Poincare bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)))
    (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B))) e.toLinearMap)
    (hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)))
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) e.symm.toLinearMap)
    (hΛ : ∀ v, v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A)) ↔
      e v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Projectivity.polarizedNativeProjectivePresentation B)))

def polarizedHodgeAbelianIso : A.abelian.scheme ≅ B.abelian.scheme :=
  Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso A.abelian B.abelian (Projectivity.polarizedNativeProjectivePresentation A)
    (Projectivity.polarizedNativeProjectivePresentation B) e he hi hΛ

instance polarizedHodgeAbelianIso_isMonHom : IsMonHom (polarizedHodgeAbelianIso A B e he hi hΛ).hom :=
  Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_isMonHom _ _ _ _ _ _ _ _

theorem polarizedHodgeAbelianIso_periods
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Projectivity.polarizedNativeProjectivePresentation A))) :
    PoincarePeriodIso.polarizedAbelianPeriodIso A B (polarizedHodgeAbelianIso A B e he hi hΛ) v = e v := by
  let PA := Projectivity.polarizedNativeProjectivePresentation A
  let PB := Projectivity.polarizedNativeProjectivePresentation B
  let f := polarizedHodgeAbelianIso A B e he hi hΛ
  let := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian PA PB f.hom
  have ht := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeComparisonMap_eq A.abelian B.abelian PA PB f.hom
  have hr := Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_rational A.abelian B.abelian PA PB e he hi hΛ
  exact LinearMap.congr_fun ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_congr _ _ ht).symm.trans hr) v

theorem polarizedHodgeAbelianIso_polarization
    (hpol : ∀ x y, Intrinsic.ChernPairing.nativePolarizationForm B (e x) (e y) = Intrinsic.ChernPairing.nativePolarizationForm A x y) :
    A.polarization.isogeny.hom ≫
        (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual (polarizedHodgeAbelianIso A B e he hi hΛ)).hom =
      (polarizedHodgeAbelianIso A B e he hi hΛ).hom ≫ B.polarization.isogeny.hom := by
  apply PoincarePeriodIso.polarization_preserved_of_period_form A B (polarizedHodgeAbelianIso A B e he hi hΛ)
  intro x y
  rw [polarizedHodgeAbelianIso_periods, polarizedHodgeAbelianIso_periods]
  exact hpol x y

theorem polarizedHodgeAbelianIso_poincare :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((Dual.UnderlyingIso.dualFamilyIso A.dual B.dual (polarizedHodgeAbelianIso A B e he hi hΛ)).hom ⊗ₘ
        (polarizedHodgeAbelianIso A B e he hi hΛ).hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare :=
  Dual.PoincareIso.dualFamilyIso_poincare A.dual B.dual (polarizedHodgeAbelianIso A B e he hi hΛ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization
