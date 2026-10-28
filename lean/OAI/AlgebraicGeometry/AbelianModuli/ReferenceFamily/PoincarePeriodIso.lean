import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps

/-! # Poincare Period Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodIso

noncomputable section

section

/-! The constructed dual isomorphism preserves the original Poincare
period pairing under the native period maps of the original schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]

def polarizedAbelianPeriodIso :=
  Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodIso A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (Polarized.Projectivity.polarizedNativeProjectivePresentation B) e

def polarizedDualPeriodIso :=
  Reference.PeriodMaps.AbelianIntrinsicAdapter.originalPeriodIso A.dual.abelian B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
    (Dual.Projectivity.dualNativeProjectivePresentation B) (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e)

theorem poincarePeriodPairing_iso
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)))
    (w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    PoincarePeriodPairing.nativePoincarePeriodPairing B (polarizedDualPeriodIso A B e v) (polarizedAbelianPeriodIso A B e w) =
      PoincarePeriodPairing.nativePoincarePeriodPairing A v w := by
  let CA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let DA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
  let DB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)
  let f : CA.toOver ⟶ CB.toOver := e.hom
  let d : DA.toOver ⟶ DB.toOver := (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e).hom
  let : IsMonHom f := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation A) (Polarized.Projectivity.polarizedNativeProjectivePresentation B) e.hom
  let : IsMonHom d := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.dual.abelian B.dual.abelian
    (Dual.Projectivity.dualNativeProjectivePresentation A) (Dual.Projectivity.dualNativeProjectivePresentation B)
    (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e).hom
  let q := HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare
  have hp := Product.ClassPairingNaturality.nativeProductClassPairing_pullback DA CA DB CB d f q
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DA v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w)
  have hd := Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality d v
  have hf := Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f w
  change Product.ClassPairingNaturality.nativeProductClassPairing DB CB q
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DB (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d v))
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CB (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f w)) = _
  rw [hd, hf]
  exact hp.symm.trans (congrArg
    (fun c => Product.ClassPairingNaturality.nativeProductClassPairing DA CA c (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods DA v) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods CA w))
    (Dual.PoincareIso.dualFamilyIso_poincare A.dual B.dual e))

end

/-! Preservation of the actual rational polarization form implies
preservation of the original polarization isogeny as a scheme morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodMaps.AbelianIntrinsicAdapter

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (e : A.abelian.scheme ≅ B.abelian.scheme) [IsMonHom e.hom]

theorem polarization_preserved_of_period_form
    (he : ∀ x y, Intrinsic.ChernPairing.nativePolarizationForm B
      (polarizedAbelianPeriodIso A B e x) (polarizedAbelianPeriodIso A B e y) =
        Intrinsic.ChernPairing.nativePolarizationForm A x y) :
    A.polarization.isogeny.hom ≫ (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e).hom =
      e.hom ≫ B.polarization.isogeny.hom := by
  let CA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let CB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B)
  let DA := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
  let DB := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation B)
  let f : CA.toOver ⟶ CB.toOver := e.hom
  let d : DA.toOver ⟶ DB.toOver := (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e).hom
  let : IsMonHom f := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.abelian B.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation A) (Polarized.Projectivity.polarizedNativeProjectivePresentation B) e.hom
  let : IsMonHom d := Reference.PeriodMaps.AbelianIntrinsicAdapter.nativeOriginalMap_isMonHom A.dual.abelian B.dual.abelian
    (Dual.Projectivity.dualNativeProjectivePresentation A) (Dual.Projectivity.dualNativeProjectivePresentation B)
    (Dual.UnderlyingIso.dualFamilyIso A.dual B.dual e).hom
  let ep := polarizedAbelianPeriodIso A B e
  have hf : Polarization.PeriodIso.nativePolarizationMap A ≫ d = f ≫ Polarization.PeriodIso.nativePolarizationMap B := by
    apply PoincarePeriodPairing.nativePoincarePeriodPairing_detects_group_maps B CA
    intro x w
    obtain ⟨y, rfl⟩ := ep.surjective w
    rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp]
    change PoincarePeriodPairing.nativePoincarePeriodPairing B
      (polarizedDualPeriodIso A B e (Polarization.PeriodIso.nativePolarizationPeriodIso A x)) (ep y) =
        PoincarePeriodPairing.nativePoincarePeriodPairing B (Polarization.PeriodIso.nativePolarizationPeriodIso B (ep x)) (ep y)
    exact (poincarePeriodPairing_iso A B e (Polarization.PeriodIso.nativePolarizationPeriodIso A x) y).trans
      ((PoincarePeriodPairing.nativePoincarePeriodPairing_polarization A x y).trans
        ((he x y).symm.trans (PoincarePeriodPairing.nativePoincarePeriodPairing_polarization B (ep x) (ep y)).symm))
  apply Over.OverMorphism.ext
  have h := congrArg Over.Hom.left hf
  simp only [Over.comp_left, Polarization.PeriodIso.nativePolarizationMap_left] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodIso
