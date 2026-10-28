import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizationHomologySimilitude
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPELHomology

/-! # Polarization Period Similitude -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The homology polarization similitude is transported to the actual
rational periods using naturality of the period marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem PolarizationPeriodSimilitude.polarizationPeriod_apply {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm A x y =
      ((1 / 2 : ℚ) • (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A - (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A).flip))
        (AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)) x)
        (AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)) y) :=
  LinearMap.congr_fun₂ (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.nativePolarizationForm_eq_poincare A) x y

theorem PolarizationPeriodSimilitude.bilinearTransport_similitude {V W V' W' : Type*}
    (B : V → V → ℚ) (C : W → W → ℚ) (B' : V' → V' → ℚ) (C' : W' → W' → ℚ)
    (e : V → V') (d : W → W') (f : V → W) (f' : V' → W')
    (hB : ∀ x y, B x y = B' (e x) (e y))
    (hC : ∀ x y, C x y = C' (d x) (d y))
    (hf : ∀ x, d (f x) = f' (e x)) (n : ℕ)
    (h : ∀ x y, C' (f' x) (f' y) = n • B' x y) (x y : V) :
    C (f x) (f y) = n • B x y := by
  rw [hC, hf, hf, h, hB]

theorem PolarizationPeriodSimilitude.polarizationPeriod_map_similitude {g N n : ℕ} {δ : Fin g → ℕ}
    (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (f : A.abelian.scheme ⟶ B.abelian.scheme) [IsMonHom f]
    (h : ∀ x y, AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing B
      (HomologicalComplex.homologyMap
        ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
          (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 x)
      (HomologicalComplex.homologyMap
        ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map
          (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 y) =
      n • AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A x y)
    (x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    let F := IntrinsicPELMaps.nativePELHom A.abelian B.abelian
      (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A) (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B) f
    AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift F x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift F y) =
      n • AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm A x y := by
  intro F
  exact PolarizationPeriodSimilitude.bilinearTransport_similitude
    (fun x y => AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm A x y) (fun x y => AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B x y)
    (fun x y => ((1 / 2 : ℚ) •
      (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A - (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing A).flip)) x y)
    (fun x y => ((1 / 2 : ℚ) •
      (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing B - (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing B).flip)) x y)
    _ _ _ _
    (PolarizationPeriodSimilitude.polarizationPeriod_apply A) (PolarizationPeriodSimilitude.polarizationPeriod_apply B)
    (IntrinsicPELHomology.nativePELHom_homology A.abelian B.abelian
      (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A) (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B) f)
    n (PolarizationHomologySimilitude.alternatingPairing_similitude _ _ _ n h) x y

variable {R : Type} [CommRing R] {g N n : ℕ} {δ : Fin g → ℕ}
  {P Q : PEL.PELFamilyData R g N Foundations.Scheme.ProjectiveSpace.complexBase} {c : R →+* R}
  (e : PELIsogenies.PELIsogeny P Q n) (hP : P.IsPEL δ c) (hQ : Q.IsPEL δ c)

theorem PELIsogenies.PELIsogeny.polarizationPeriod_similitude
    (x y : AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native P.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (P.toPolarized hP)))) :
    let f := IntrinsicPELMaps.nativePELHom P.abelian Q.abelian
      (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (P.toPolarized hP))
      (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (Q.toPolarized hQ)) e.isogeny.hom
    AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (Q.toPolarized hQ) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      n • AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm (P.toPolarized hP) x y :=
  PolarizationPeriodSimilitude.polarizationPeriod_map_similitude (P.toPolarized hP) (Q.toPolarized hQ) e.isogeny.hom
    (e.polarizationHomology_similitude hP hQ) x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
