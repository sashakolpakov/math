import OAI.RepresentationTheory.Theta.Adelic.LocalGenerators

/-! # Polarization Lift -/

namespace OAI.RepresentationTheory.Theta.Adelic.PolarizationLift

noncomputable section

/-! Every finite symplectic change of polarization has an actual unitary
oscillator lift, constructed from quadratic, linear, and Fourier generators. -/

open OAI.RepresentationTheory.Theta.Adelic.LocalGenerators OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration

theorem localProjection_surjective
    {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] [CompleteSpace k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hk : ¬ DiscreteTopology k)
    (hn : ∃ x : k, ψ x ≠ 1) (N : ℕ) : Function.Surjective (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ) := by
  obtain ⟨w, hw⟩ := LocalGenerators.exists_weyl_lift ψ hc hu hk hn (N := N)
  have hr : (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ).range = ⊤ := by
    apply Weil.AdelicSplitting.SymplecticGeneration.subgroup_eq_top_of_generators
    · intro B hB
      exact ⟨LocalGenerators.upperLift ψ hc hu w ⟨B, hB⟩, LocalGenerators.upperLift_projection ψ hc hu w hw ⟨B, hB⟩⟩
    · intro A
      exact ⟨Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A, rfl⟩
    · exact ⟨w, hw⟩
  intro g
  exact show g ∈ (Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ).range from hr ▸ Subgroup.mem_top g

end

end OAI.RepresentationTheory.Theta.Adelic.PolarizationLift
