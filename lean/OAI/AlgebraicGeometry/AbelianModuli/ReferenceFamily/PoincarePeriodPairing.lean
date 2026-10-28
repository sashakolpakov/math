import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PeriodIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactPolarizationPairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality

/-! # Poincare Period Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing

noncomputable section

section

/-! The original Poincare class pairs the actual rational periods of
the dual and the abelian scheme. Its pullback by the original
polarization isogeny is precisely the native polarization form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

def nativePoincarePeriodPairing :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)) →ₗ[ℚ]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) →ₗ[ℚ] ℚ :=
  (Product.ClassPairingNaturality.nativeProductClassPairing (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A))
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
    (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)).compl₁₂
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A))).toLinearMap
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).toLinearMap

theorem nativePoincarePeriodPairing_polarization
    (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    nativePoincarePeriodPairing A (Polarization.PeriodIso.nativePolarizationPeriodIso A x) y = Intrinsic.ChernPairing.nativePolarizationForm A x y := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  let D := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)
  let f := Polarization.PeriodIso.nativePolarizationMap A
  let q := HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare
  have hc : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ 𝟙 B.toOver).left q = Polarization.Adjoints.polarizationBiextensionClass A := by
    unfold Polarization.Adjoints.polarizationBiextensionClass
    apply congrArg (fun h => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h q)
    change (f ⊗ₘ 𝟙 B.toOver).left = (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left
    have hf : f = A.polarization.isogeny.hom := by
      apply Over.OverMorphism.ext
      exact Polarization.PeriodIso.nativePolarizationMap_left A
    rw [hf]
    rfl
  have hp := Product.ClassPairingNaturality.nativeProductClassPairing_pullback B B D B f (𝟙 B.toOver) q
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y)
  rw [Product.ClassPairingNaturality.nativePointHomology_id] at hp
  have hn := Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f x
  have hform := LinearMap.congr_fun
    (LinearMap.congr_fun (ExactPolarizationPairing.nativePolarizationForm_eq_poincare_exact A) x) y
  change Product.ClassPairingNaturality.nativeProductClassPairing D B q
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods D (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x)) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y) = _
  rw [hn]
  exact hp.symm.trans ((congrArg
    (fun c => Product.ClassPairingNaturality.nativeProductClassPairing B B c (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y)) hc).trans hform.symm)

end

/-! The actual Poincare pairing separates periods in both factors.
Consequently it detects algebraic group maps into the original dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem nativePoincarePeriodPairing_left_separating
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)))
    (hv : ∀ w, nativePoincarePeriodPairing A v w = 0) : v = 0 := by
  let e := Polarization.PeriodIso.nativePolarizationPeriodIso A
  have hz : e.symm v = 0 := by
    apply Intrinsic.ChernPeriod.nativePolarizationForm_separating A
    intro w
    exact (nativePoincarePeriodPairing_polarization A (e.symm v) w).symm.trans
      ((congrArg (fun z => nativePoincarePeriodPairing A z w) (e.apply_symm_apply v)).trans (hv w))
  exact e.symm.injective (hz.trans e.symm.map_zero.symm)

theorem nativePoincarePeriodPairing_right_separating
    (w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
    (hw : ∀ v, nativePoincarePeriodPairing A v w = 0) : w = 0 := by
  have ha : (Intrinsic.ChernPairing.nativePolarizationForm A).IsAlt := Intrinsic.ChernPairing.nativePolarizationForm_alternating A
  apply Intrinsic.ChernPeriod.nativePolarizationForm_separating A
  intro v
  have hv : Intrinsic.ChernPairing.nativePolarizationForm A v w = 0 :=
    (nativePoincarePeriodPairing_polarization A v w).symm.trans (hw _)
  exact (ha.neg v w).symm.trans (congrArg Neg.neg hv) |>.trans neg_zero

theorem nativePoincarePeriodPairing_left_ext
    (v v' : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)))
    (hv : ∀ w, nativePoincarePeriodPairing A v w = nativePoincarePeriodPairing A v' w) : v = v' := by
  apply sub_eq_zero.mp
  apply nativePoincarePeriodPairing_left_separating A
  intro w
  change (nativePoincarePeriodPairing A (v - v')) w = 0
  rw [map_sub, LinearMap.sub_apply, hv w, sub_self]

theorem nativePoincarePeriodPairing_detects_group_maps (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f h : B.toOver ⟶ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.dual.abelian (Dual.Projectivity.dualNativeProjectivePresentation A)).toOver)
    [IsMonHom f] [IsMonHom h]
    (hfh : ∀ v w, nativePoincarePeriodPairing A (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f v) w =
      nativePoincarePeriodPairing A (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift h v) w) : f = h := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful f h
  apply LinearMap.ext
  intro v
  exact nativePoincarePeriodPairing_left_ext A _ _ (hfh v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincarePeriodPairing
