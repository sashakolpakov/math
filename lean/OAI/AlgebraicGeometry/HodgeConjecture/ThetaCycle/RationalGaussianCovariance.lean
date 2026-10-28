import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalRealOperator
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalOscillator
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCoverOperator

/-! # Rational Gaussian Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussianCovariance.CM

noncomputable section

/-! ThetaCycle: the full Gaussian law of the already constructed rational
adelic oscillator, with the explicit classical/oscillator phase swap. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

theorem restricted_rational_oscillator_projection_at
    (F : Type) [Field F] [NumberField F] (N : ℕ) (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.projectionAt F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) v (RationalOscillator.CM.restrictedFieldRationalOscillator F N γ v) =
      RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal F N v γ := by
  have h := RationalOscillator.CM.field_rational_oscillator_covers F N γ
  rw [← RationalOscillator.CM.restricted_field_rational_oscillator_assemble] at h
  exact congrArg (fun b : RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.AdelicSymplectic F N => b v) h

theorem rational_real_symplectic_projection (N : ℕ) (v : InfinitePlace ℚ) (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ N) :
    RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap (RationalRealOperator.CM.rationalRealCoordinate v) N (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.rationalSymplecticLocal ℚ N (.inl v) γ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ := by
  apply Subtype.ext
  ext i j
  exact (RationalRealOperator.CM.rationalRealCoordinate v).toRingHom.map_rat_algebraMap (γ.val i j)

theorem map_symplectic_phase_swap {I R S : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [CommRing S] (f : R →+* S) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I R) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f (OscillatorPhaseOrder.CM.swapSymplecticPhase g) = OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp f g) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

local instance (v : InfinitePlace ℚ) : MeasurableSpace v.Completion := borel _
local instance (v : InfinitePlace ℚ) : BorelSpace v.Completion := ⟨rfl⟩

def classicalRationalRealOscillator (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (v : InfinitePlace ℚ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  RationalRealOperator.CM.rationalRealOscillator N v (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) (.inl v))

theorem classical_rational_real_oscillator_projection (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (v : InfinitePlace ℚ) :
    RepresentationTheory.Weil.Local.OscillatorProjection.Construction.oscillatorProjection ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (classicalRationalRealOscillator N γ v) =
      OscillatorPhaseOrder.CM.swapSymplecticPhase (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ) := by
  change (classicalRationalRealOscillator N γ v).val.1 = _
  rw [classicalRationalRealOscillator, RationalRealOperator.CM.rational_real_oscillator_projection]
  have h := restricted_rational_oscillator_projection_at ℚ N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) (.inl v)
  change (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) (.inl v)).val.1 = _ at h
  rw [h, rational_real_symplectic_projection, map_symplectic_phase_swap]

def rationalGaussianCoefficient (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : ℂ :=
  RealGaussianCoefficient.CM.realGaussianCoefficient (classicalRationalRealOscillator N γ Rat.infinitePlace) Z

theorem rational_gaussian_coefficient_place (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (v : InfinitePlace ℚ) :
    RealGaussianCoefficient.CM.realGaussianCoefficient (classicalRationalRealOscillator N γ v) Z = rationalGaussianCoefficient N γ Z :=
  congrArg (fun w => RealGaussianCoefficient.CM.realGaussianCoefficient (classicalRationalRealOscillator N γ w) Z)
    (Subsingleton.elim v Rat.infinitePlace)

theorem rational_gaussian_coefficient_ne_zero (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) : rationalGaussianCoefficient N γ Z ≠ 0 :=
  RealGaussianCoefficient.CM.real_gaussian_coefficient_ne_zero _ _ (classical_rational_real_oscillator_projection N γ Rat.infinitePlace) Z

theorem rational_archimedean_gaussian_action (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) (v : InfinitePlace ℚ) :
    (FiniteCoverOperator.CM.archimedeanCoverOperator ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ)
        (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ))
        (RationalGaussian.CM.rationalArchimedeanGaussian N Z z)) v =
      (rationalGaussianCoefficient N γ Z * Complex.exp (-(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z z z)) •
        RationalGaussian.CM.rationalArchimedeanGaussian N ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) v := by
  apply (RationalRealOperator.CM.rationalRealTestTransport N v).injective
  rw [map_smul, RationalRealOperator.CM.rational_real_test_gaussian]
  change RationalRealOperator.CM.rationalRealTestTransport N v
    ((RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) (.inl v)).val.2
      (RationalGaussian.CM.rationalArchimedeanGaussian N Z z v)) = _
  rw [← RationalRealOperator.CM.rational_real_oscillator_operator, RationalRealOperator.CM.rational_real_test_gaussian]
  have h := RealGaussianCovariance.CM.real_oscillator_full_gaussian_covariance (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) γ)
    (classicalRationalRealOscillator N γ v) (classical_rational_real_oscillator_projection N γ v) Z z
  rw [rational_gaussian_coefficient_place] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussianCovariance.CM
