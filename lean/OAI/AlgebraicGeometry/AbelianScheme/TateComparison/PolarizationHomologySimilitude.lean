import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicHomologyPower
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELPolarizationClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm

/-! # Polarization Homology Similitude -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual Poincare similitude identity induces the same multiplier
on the rational homology polarization pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

theorem PolarizationHomologySimilitude.nativeProductPairing_similitude (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver) (n : ℕ)
    (p : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.toOver ⊗ A.toOver).left)
    (r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (B.toOver ⊗ B.toOver).left)
    (hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ f).left r =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (((𝟙 A.toOver) ^ n) ⊗ₘ 𝟙 A.toOver).left p)
    (x y : AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver)) :
    AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing B B r
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 x)
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 y) =
      n • AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing A A p x y := by
  have hf := AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing_pullback A A B B f f r x y
  have hn := AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing_pullback A A A A ((𝟙 A.toOver) ^ n) (𝟙 A.toOver) p x y
  rw [IntrinsicHomologyPower.nativePointHomology_pow, AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativePointHomology_id, map_nsmul, LinearMap.smul_apply] at hn
  exact hf.symm.trans ((congrArg (fun z => AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing A A z x y) hp).trans hn)

theorem PolarizationHomologySimilitude.alternatingPairing_similitude {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (B : LinearMap.BilinForm ℚ V) (C : LinearMap.BilinForm ℚ W)
    (f : V → W) (n : ℕ) (h : ∀ x y, C (f x) (f y) = n • B x y) (x y : V) :
    ((1 / 2 : ℚ) • (C - C.flip)) (f x) (f y) =
      n • (((1 / 2 : ℚ) • (B - B.flip)) x y) := by
  change (1 / 2 : ℚ) * (C (f x) (f y) - C (f y) (f x)) =
    n • ((1 / 2 : ℚ) * (B x y - B y x))
  rw [h, h]
  simp only [nsmul_eq_mul]
  ring

variable {R : Type} [CommRing R] {g N n : ℕ} {δ : Fin g → ℕ}
  {P Q : PEL.PELFamilyData R g N Foundations.Scheme.ProjectiveSpace.complexBase} {c : R →+* R}
  (e : PELIsogenies.PELIsogeny P Q n) (hP : P.IsPEL δ c) (hQ : Q.IsPEL δ c)

theorem PELIsogenies.PELIsogeny.polarizationHomology_similitude
    (x y : AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace P.abelian.scheme)) :
    AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (Q.toPolarized hQ)
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.isogeny.hom))) 1 x)
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.isogeny.hom))) 1 y) =
      n • AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (P.toPolarized hP) x y :=
  PolarizationHomologySimilitude.nativeProductPairing_similitude
    (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native P.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (P.toPolarized hP)))
    (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native Q.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (Q.toPolarized hQ)))
    e.isogeny.hom n P.polarizationClass Q.polarizationClass e.polarizationClass_similitude x y

theorem PELIsogenies.PELIsogeny.alternatingPolarizationHomology_similitude
    (x y : AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace P.abelian.scheme)) :
    ((1 / 2 : ℚ) • (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (Q.toPolarized hQ) -
      (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (Q.toPolarized hQ)).flip))
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.isogeny.hom))) 1 x)
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous e.isogeny.hom))) 1 y) =
      n • (((1 / 2 : ℚ) • (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (P.toPolarized hP) -
        (AbelianModuli.ReferenceFamily.Polarization.HomologyForm.polarizationHomologyPairing (P.toPolarized hP)).flip)) x y) :=
  PolarizationHomologySimilitude.alternatingPairing_similitude _ _ _ n (e.polarizationHomology_similitude hP hQ) x y

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
