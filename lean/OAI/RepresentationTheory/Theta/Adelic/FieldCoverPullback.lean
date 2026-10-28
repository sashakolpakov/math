import OAI.RepresentationTheory.Theta.Adelic.FieldCoverTopology
import OAI.RepresentationTheory.Weil.Local.FieldOscillator

/-! # Field Cover Pullback -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback

noncomputable section

/-! Continuous pullback of the actual native oscillator cover, with
explicit projection and test-function operator formulas. -/

open OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction OAI.RepresentationTheory.Theta.Adelic.FieldCoverTopology

def coverCharacterCongr
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {N : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N η := by
  subst η
  exact ContinuousMonoidHom.id _

theorem coverCharacterCongr_projection
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {N : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k N η (coverCharacterCongr h a) = Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a := by
  subst η
  rfl

theorem coverCharacterCongr_operator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {N : ℕ} {ψ η : AddChar k ℂ} (h : ψ = η) (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator k N η (coverCharacterCongr h a) = Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a := by
  subst η
  rfl

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ)

def fieldCoverPullback : Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ :=
  (coverCharacterCongr (Weil.Local.FieldOscillator.Construction.fieldCharacter_symm e ψ)).comp
    (FieldCoverTopology.fieldCoverContinuous e.symm hi he N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ))

theorem fieldCoverPullback_projection (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)) :
    Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (fieldCoverPullback e he hi N ψ a) =
      Weil.Local.FieldFourier.Construction.fieldSymplecticMap e.symm N (Weil.AdelicSplitting.Oscillator.Construction.localProjection l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a) := by
  exact coverCharacterCongr_projection (Weil.Local.FieldOscillator.Construction.fieldCharacter_symm e ψ)
    (FieldCoverTopology.fieldCoverContinuous e.symm hi he N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a)

theorem fieldCoverPullback_operator (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (fieldCoverPullback e he hi N ψ a) f =
      (Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N)).symm
        (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a (Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) f)) := by
  exact congrArg (fun R : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N => R f)
    (coverCharacterCongr_operator (Weil.Local.FieldOscillator.Construction.fieldCharacter_symm e ψ)
      (FieldCoverTopology.fieldCoverContinuous e.symm hi he N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a))

theorem fieldCoverPullback_transport (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) :
    fieldCoverPullback e he hi N ψ (FieldCoverTopology.fieldCoverContinuous e he hi N ψ a) = a := by
  apply Subtype.ext
  apply Prod.ext
  · exact (fieldCoverPullback_projection e he hi N ψ _).trans (Weil.Local.FieldOscillator.Construction.fieldSymplecticMap_symm e N a.val.1)
  · apply LinearEquiv.ext
    intro f
    change Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (fieldCoverPullback e he hi N ψ (FieldCoverTopology.fieldCoverContinuous e he hi N ψ a)) f = a.val.2 f
    rw [fieldCoverPullback_operator]
    change (Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N)).symm
      ((Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi N ψ a).val.2 (Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) f)) = a.val.2 f
    rw [Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport_apply, LinearEquiv.symm_apply_apply]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback
