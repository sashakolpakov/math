import OAI.RepresentationTheory.Theta.Adelic.TestTransportEnergy
import OAI.RepresentationTheory.Weil.Local.FieldOscillator
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator

/-! # Field Cover Topology -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldCoverTopology

noncomputable section

/-! The actual oscillator transport between topological local fields is
continuous for the specified strong operator topologies. -/

open OAI.RepresentationTheory.Weil.Local.FieldOscillator.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction OAI.RepresentationTheory.Theta.Adelic.TestTransportEnergy

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]

omit [LocallyCompactSpace k] [LocallyCompactSpace l] [MeasurableSpace k] [BorelSpace k]
  [MeasurableSpace l] [BorelSpace l] [SecondCountableTopology k] [SecondCountableTopology l] in
theorem fieldSymplecticMap_continuous (e : k ≃+* l) (he : Continuous e) (N : ℕ) :
    Continuous (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact he.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

theorem fieldOscillatorTransport_continuous
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ) :
    Continuous (Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi N ψ) := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  let C := Weil.Local.FieldCoordinates.Construction.testSpaceTransport p
  let T := Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi N ψ
  let r := Real.sqrt (TestTransportEnergy.transportEnergyScale p : ℝ)
  have hobs (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat l N) :
      Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy l N ((T a).val.2 f - h)) =
        r * Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (a.val.2 (C.symm f) - C.symm h)) := by
    have heq : (T a).val.2 f - h = C (a.val.2 (C.symm f) - C.symm h) := by
      rw [map_sub, C.apply_symm_apply]
      rfl
    rw [heq]
    exact TestTransportEnergy.testSpaceTransport_sqrt_energy p _
  have hiobs (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat l N) :
      Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy l N ((T a).val.2.symm f - h)) =
        r * Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (a.val.2.symm (C.symm f) - C.symm h)) := by
    have hh := hobs a⁻¹ f h
    rw [map_inv] at hh
    exact hh
  have ho : Continuous (Weil.AdelicSplitting.Oscillator.Construction.localObservations k N ψ) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · change Continuous (fun a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ => Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a))
    exact (fieldSymplecticMap_continuous e he N).comp (Weil.AdelicSplitting.Oscillator.Construction.localProjection_continuous k N ψ)
  · apply Continuous.prodMk
    · apply continuous_pi
      rintro ⟨f, h⟩
      change Continuous (fun a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ => Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy l N ((T a).val.2 f - h)))
      simp_rw [hobs]
      exact continuous_const.mul ((continuous_apply (C.symm f, C.symm h)).comp
        (continuous_fst.comp (continuous_snd.comp ho)))
    · apply continuous_pi
      rintro ⟨f, h⟩
      change Continuous (fun a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ => Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy l N ((T a).val.2.symm f - h)))
      simp_rw [hiobs]
      exact continuous_const.mul ((continuous_apply (C.symm f, C.symm h)).comp
        (continuous_snd.comp (continuous_snd.comp ho)))

def fieldCoverContinuous
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ) :
    Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) :=
  ⟨Weil.Local.FieldOscillator.Construction.fieldOscillatorTransport e he hi N ψ, fieldOscillatorTransport_continuous e he hi N ψ⟩

end

end OAI.RepresentationTheory.Theta.Adelic.FieldCoverTopology
