import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussian
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCovariance
import OAI.RepresentationTheory.Weil.Local.FieldOscillator

/-! # Rational Real Operator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalRealOperator.CM

noncomputable section

/-! ThetaCycle: transport the actual rational archimedean oscillator to the
standard real presentation, preserving its operator and Gaussian values. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction

def oscillatorCharacterEquiv {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (N : ℕ) {ψ χ : AddChar k ℂ} (h : ψ = χ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator k N ψ ≃* RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator k N χ := by
  subst χ
  exact MulEquiv.refl _

theorem oscillator_character_equiv_projection {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (N : ℕ) {ψ χ : AddChar k ℂ} (h : ψ = χ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator k N ψ) : (oscillatorCharacterEquiv N h a).val.1 = a.val.1 := by
  subst χ
  rfl

theorem oscillator_character_equiv_operator {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (N : ℕ) {ψ χ : AddChar k ℂ} (h : ψ = χ)
    (a : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator k N ψ) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (oscillatorCharacterEquiv N h a).val.2 f = a.val.2 f := by
  subst χ
  rfl

def rationalRealCoordinate (v : InfinitePlace ℚ) : v.Completion ≃+* ℝ :=
  ringEquivRealOfIsReal (IsTotallyReal.isReal v)

theorem rational_real_coordinate_continuous (v : InfinitePlace ℚ) :
    Continuous (rationalRealCoordinate v) :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous

theorem rational_real_coordinate_inverse_continuous (v : InfinitePlace ℚ) :
    Continuous (rationalRealCoordinate v).symm :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous

local instance (v : InfinitePlace ℚ) : MeasurableSpace v.Completion := borel _
local instance (v : InfinitePlace ℚ) : BorelSpace v.Completion := ⟨rfl⟩
local instance (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph.isEmbedding.secondCountableTopology

theorem rational_real_character_identification (v : InfinitePlace ℚ) :
    RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldCharacter (rationalRealCoordinate v)
        (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter ℚ (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)) = RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1 := by
  ext t
  change RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter ℚ (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)
    ((rationalRealCoordinate v).symm t) = RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1 t
  rw [RealCharacterNormalization.CM.field_adelic_character_standard_real_coordinate, RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter_apply]
  congr 1
  push_cast
  ring

def rationalRealTestTransport (N : ℕ) (v : InfinitePlace ℚ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat v.Completion N ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ N :=
  RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport (RepresentationTheory.Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv (rationalRealCoordinate v)
    (rational_real_coordinate_continuous v) (rational_real_coordinate_inverse_continuous v) N)

def rationalRealOscillator (N : ℕ) (v : InfinitePlace ℚ)
    (a : RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.CoverAt ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Oscillator ℝ N (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) :=
  oscillatorCharacterEquiv N (rational_real_character_identification v)
    (RepresentationTheory.Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport (rationalRealCoordinate v) (rational_real_coordinate_continuous v)
      (rational_real_coordinate_inverse_continuous v) N
      (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter ℚ (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)) a)

theorem rational_real_oscillator_operator (N : ℕ) (v : InfinitePlace ℚ)
    (a : RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.CoverAt ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat v.Completion N) :
    (rationalRealOscillator N v a).val.2 (rationalRealTestTransport N v f) =
      rationalRealTestTransport N v (a.val.2 f) := by
  rw [rationalRealOscillator, oscillator_character_equiv_operator]
  exact RepresentationTheory.Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_apply _ _ _ N _ a f

theorem rational_real_oscillator_projection (N : ℕ) (v : InfinitePlace ℚ)
    (a : RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.CoverAt ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ) (.inl v)) :
    (rationalRealOscillator N v a).val.1 = RepresentationTheory.Weil.Local.FieldFourier.Construction.fieldSymplecticMap (rationalRealCoordinate v) N a.val.1 := by
  rw [rationalRealOscillator, oscillator_character_equiv_projection]
  rfl

theorem rational_real_test_gaussian (N : ℕ) (v : InfinitePlace ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    rationalRealTestTransport N v (RationalGaussian.CM.rationalArchimedeanGaussian N Z z v) = RealGaussianCoefficient.CM.realSiegelGaussian Z z := by
  apply Subtype.ext
  funext x
  rw [rationalRealTestTransport, RepresentationTheory.Weil.Local.FieldCoordinates.Construction.testSpaceTransport_apply, RationalGaussian.CM.rationalArchimedeanGaussian,
    RationalGaussian.CM.real_completion_gaussian_apply, RealGaussianCoefficient.CM.real_siegel_gaussian_apply]
  congr 1
  funext i
  exact (rationalRealCoordinate v).apply_symm_apply (x i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalRealOperator.CM
