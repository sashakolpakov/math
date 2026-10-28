import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality

/-! # Homology Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The originally constructed period form is the alternating part
of evaluation of the original lambda-Poincare class. This removes its
dependence on the ample witness and gives the geometric Rosati adjoint
on actual singular homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}

def Polarization.HomologyForm.polarizationHomologyPairing (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase) :
    HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme) →ₗ[ℚ]
      HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme) →ₗ[ℚ] ℚ :=
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  Product.ClassPairingNaturality.nativeProductClassPairing B B (Polarization.Adjoints.polarizationBiextensionClass A)

theorem Polarization.HomologyForm.nativePolarizationForm_eq_poincare
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase) :
    Intrinsic.ChernPairing.nativePolarizationForm A =
      ((1 / 2 : ℚ) • (Polarization.HomologyForm.polarizationHomologyPairing A - (Polarization.HomologyForm.polarizationHomologyPairing A).flip)).compl₁₂
        (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods
          (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).toLinearMap
        (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods
          (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))).toLinearMap := by
  let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  obtain ⟨e⟩ := Polarization.Biextension.polarizationLineBundle_poincare A
  have h := BiextensionPeriodPairing.nativeBiextensionHomologyPairing_eq B (Intrinsic.ChernPairing.polarizationLineBundle A) (Polarization.Biextension.polarizationOriginalBiextension A) e
  have hc := congrArg (Product.ClassPairingNaturality.nativeProductClassPairing B B) (Polarization.Biextension.polarizationOriginalBiextension_class A)
  exact congrArg (fun b => ((1 / 2 : ℚ) • (b - b.flip)).compl₁₂
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).toLinearMap
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).toLinearMap) (h.symm.trans hc)

theorem Polarization.HomologyForm.nativePolarizationForm_of_witness
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left)
    (B : HilbertConstruction.Line.Bundles.LineBundle (A.abelian.scheme ⊗ A.abelian.scheme).left)
    (hB : HilbertConstruction.Line.Bundles.LineBundle.classOf B = Polarization.Adjoints.polarizationBiextensionClass A)
    (e : ((B.tensor (L.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
      (L.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
        (L.pullback (MonObj.mul (X := A.abelian.scheme)).left).sheaf) :
    Intrinsic.ChernPairing.nativeChernForm (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)) L =
      Intrinsic.ChernPairing.nativePolarizationForm A := by
  let C := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
  have h := BiextensionPeriodPairing.nativeBiextensionHomologyPairing_eq C L B e
  have hc := congrArg (Product.ClassPairingNaturality.nativeProductClassPairing C C) hB
  exact (congrArg (fun b => ((1 / 2 : ℚ) • (b - b.flip)).compl₁₂
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods C).toLinearMap
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods C).toLinearMap) (h.symm.trans hc)).trans
      (Polarization.HomologyForm.nativePolarizationForm_eq_poincare A).symm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ActionData.RosatiConjugation.homology_adjoint
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (a : NumberField.RingOfIntegers E)
    (x y : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme)) :
    Polarization.HomologyForm.polarizationHomologyPairing A
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous
        (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))))) 1 x) y =
    Polarization.HomologyForm.polarizationHomologyPairing A x
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (ρ.map a)))) 1 y) :=
  Product.ClassPairingNaturality.nativeProductClassPairing_adjoint
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))
    (Polarization.Adjoints.polarizationBiextensionClass A) (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a)) (ρ.map a)
    (ActionData.RosatiConjugation.biextension_adjoint A ρ hρ a) x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
