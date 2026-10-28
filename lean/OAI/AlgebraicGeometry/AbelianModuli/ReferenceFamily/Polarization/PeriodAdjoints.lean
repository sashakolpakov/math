import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.HomologyForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers

/-! # Period Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual algebraic Rosati equation is transported to rational
native periods by the proved naturality of their homology marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

theorem Polarization.PeriodAdjoints.nativeEndomorphism_pointMap {d : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme d Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) (f : A.scheme ⟶ A.scheme) :
    TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A P f)) =
      TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f) := by
  apply TopCat.ext
  intro p
  apply Over.OverMorphism.ext
  change p.left ≫ (𝟙 _ ≫ f.left ≫ 𝟙 _) = p.left ≫ f.left
  simp only [Category.id_comp]
  exact congrArg (fun a => p.left ≫ a) (Category.comp_id f.left)

theorem Polarization.PeriodAdjoints.alternatingBilinear_adjoint {V : Type} [AddCommGroup V] [Module ℚ V]
    (b : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (f g : V → V)
    (hfg : ∀ x y, b (f x) y = b x (g y)) (hgf : ∀ x y, b (g x) y = b x (f y))
    (x y : V) :
    ((1 / 2 : ℚ) • (b - b.flip)) (f x) y = ((1 / 2 : ℚ) • (b - b.flip)) x (g y) := by
  change (1 / 2 : ℚ) * (b (f x) y - b y (f x)) = (1 / 2 : ℚ) * (b x (g y) - b (g y) x)
  rw [hfg, hgf]

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}

theorem Polarization.PeriodAdjoints.integralConjugation_involutive (a : NumberField.RingOfIntegers E) :
    NumberField.IsCMField.ringOfIntegersComplexConj E
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) = a := by
  apply NumberField.RingOfIntegers.ext
  exact NumberField.IsCMField.complexConj_apply_apply E a

theorem ActionData.RosatiConjugation.alternating_homology_adjoint
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (a : NumberField.RingOfIntegers E)
    (x y : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.abelian.scheme)) :
    ((1 / 2 : ℚ) • (Polarization.HomologyForm.polarizationHomologyPairing A - (Polarization.HomologyForm.polarizationHomologyPairing A).flip))
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous
        (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))))) 1 x) y =
    ((1 / 2 : ℚ) • (Polarization.HomologyForm.polarizationHomologyPairing A - (Polarization.HomologyForm.polarizationHomologyPairing A).flip)) x
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (ρ.map a)))) 1 y) := by
  apply Polarization.PeriodAdjoints.alternatingBilinear_adjoint
  · exact ActionData.RosatiConjugation.homology_adjoint A ρ hρ a
  · intro x y
    have h := ActionData.RosatiConjugation.homology_adjoint A ρ hρ
      (NumberField.IsCMField.ringOfIntegersComplexConj E a) x y
    rw [Polarization.PeriodAdjoints.integralConjugation_involutive] at h
    exact h

theorem ActionData.RosatiConjugation.period_adjoint
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : ActionData.RosatiConjugation A ρ) (a : NumberField.RingOfIntegers E) :
    let B := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    ∀ x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B,
      Intrinsic.ChernPairing.nativePolarizationForm A
        (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))) x) y =
      Intrinsic.ChernPairing.nativePolarizationForm A x (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian
        (Polarized.Projectivity.polarizedNativeProjectivePresentation A) (ρ.map a)) y) := by
  intro B x y
  let F := Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
  let G := Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter.nativeEndomorphism A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) (ρ.map a)
  have hf := Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality F x
  have hg := Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality G y
  rw [Polarization.PeriodAdjoints.nativeEndomorphism_pointMap] at hf hg
  rw [Polarization.HomologyForm.nativePolarizationForm_eq_poincare]
  change ((1 / 2 : ℚ) • (Polarization.HomologyForm.polarizationHomologyPairing A - (Polarization.HomologyForm.polarizationHomologyPairing A).flip))
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift F x)) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y) =
    ((1 / 2 : ℚ) • (Polarization.HomologyForm.polarizationHomologyPairing A - (Polarization.HomologyForm.polarizationHomologyPairing A).flip))
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift G y))
  rw [hf, hg]
  exact ActionData.RosatiConjugation.alternating_homology_adjoint A ρ hρ a (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B x) (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
