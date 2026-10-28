import OAI.RepresentationTheory.Weil.Local.FieldOscillator
import OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification
import OAI.RepresentationTheory.Weil.Local.RealBareKernel
import OAI.RepresentationTheory.Weil.Local.ComplexBareKernel

/-! # Archimedean Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel.Construction

noncomputable section

/-! Bare-kernel signs for every archimedean field presentation, independently of its chosen norm. -/

theorem fieldCharacter_continuous {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he' : Continuous e.symm) (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) :
    Continuous (fun t => FieldFourier.Construction.fieldCharacter e ψ t) := hc.comp he'

theorem fieldCharacter_unitary {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) :
    ∀ t, ‖FieldFourier.Construction.fieldCharacter e ψ t‖ = 1 := fun t => hu (e.symm t)

theorem fieldCharacter_nontrivial {k l : Type} [Field k] [Field l]
    (e : k ≃+* l) (ψ : AddChar k ℂ) (hn : ∃ t, ψ t ≠ 1) :
    ∃ t, FieldFourier.Construction.fieldCharacter e ψ t ≠ 1 := by
  obtain ⟨t, ht⟩ := hn
  refine ⟨e t, ?_⟩
  change ψ (e.symm (e t)) ≠ 1
  rwa [e.symm_apply_apply]

theorem archimedean_metaplectic_kernel_sign
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1) {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.val.2 f = ε • f := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  rcases ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, he'⟩ | ⟨e, he, he'⟩
  · let b := FieldOscillator.Construction.fieldMetaplecticTransport e he he' n ψ a
    have hb : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (FieldFourier.Construction.fieldCharacter e ψ) b = 1 := by
      change OscillatorProjection.Construction.oscillatorProjection ℝ n (FieldFourier.Construction.fieldCharacter e ψ) (FieldOscillator.Construction.fieldOscillatorTransport e he he' n ψ a.val) = 1
      rw [FieldOscillator.Construction.fieldOscillatorTransport_projection]
      change FieldFourier.Construction.fieldSymplecticMap e n (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a) = 1
      rw [ha, map_one]
    obtain ⟨ε, hε, hs⟩ := RealBareKernel.Construction.real_metaplectic_kernel_sign (FieldFourier.Construction.fieldCharacter e ψ)
      (fieldCharacter_continuous e he' ψ hc) (fieldCharacter_unitary e ψ hu)
      (fieldCharacter_nontrivial e ψ hn) b hb
    exact ⟨ε, hε, FieldOscillator.Construction.fieldMetaplecticTransport_scalar_pullback e he he' n ψ a ε hs⟩
  · let b := FieldOscillator.Construction.fieldMetaplecticTransport e he he' n ψ a
    have hb : FunctionsMetaplectic.Construction.metaplecticProjection ℂ n (FieldFourier.Construction.fieldCharacter e ψ) b = 1 := by
      change OscillatorProjection.Construction.oscillatorProjection ℂ n (FieldFourier.Construction.fieldCharacter e ψ) (FieldOscillator.Construction.fieldOscillatorTransport e he he' n ψ a.val) = 1
      rw [FieldOscillator.Construction.fieldOscillatorTransport_projection]
      change FieldFourier.Construction.fieldSymplecticMap e n (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a) = 1
      rw [ha, map_one]
    obtain ⟨ε, hε, hs⟩ := ComplexBareKernel.Construction.complex_metaplectic_kernel_sign (FieldFourier.Construction.fieldCharacter e ψ)
      (fieldCharacter_continuous e he' ψ hc) (fieldCharacter_unitary e ψ hu)
      (fieldCharacter_nontrivial e ψ hn) b hb
    exact ⟨ε, hε, FieldOscillator.Construction.fieldMetaplecticTransport_scalar_pullback e he he' n ψ a ε hs⟩

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel.Construction
