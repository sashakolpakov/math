import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanBase
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanQuadratic
import OAI.RepresentationTheory.Weil.UnitarySplitting.GeneratorSurjectivity

/-! # Surjectivity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Surjectivity.Construction

noncomputable section

/-! Surjectivity of the actual oscillator projection for every base field
admitted by the quadratic-extension hypotheses of UnitarySplitting. -/

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
variable (σ : E ≃ₐ[F] E)
variable (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun t : F => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
variable (hn : ∃ t, ψ t ≠ 1)

include hF hc hu hn in
theorem circleProjection_surjective_archimedean
    (e : ℝ ≃+* F) (he : Continuous e) (hei : Continuous e.symm) :
    Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) := by
  apply GeneratorSurjectivity.Construction.circleProjection_surjective_of_generators σ H K c ψ
  · obtain ⟨U, henergy, hcov⟩ := ArchimedeanFourier.Construction.exists_archimedean_unitary_fourier hF e he hei ψ hc hu hn
      (d := m * n)
    exact ⟨FrameTransport.Construction.frameOscillatorLift σ H K c hF ψ hc hu (FrameTransport.Construction.rotationSymplectic (m * n))
      U henergy hcov, rfl⟩
  · intro B
    exact ⟨FrameTransport.Construction.frameOscillatorLift σ H K c hF ψ hc hu (FrameTransport.Construction.shearSymplectic B)
      (ArchimedeanQuadratic.Construction.archimedeanQuadraticOperator e he hei ψ hc hu B.val)
      (ArchimedeanQuadratic.Construction.archimedeanQuadraticOperator_unitary e he hei ψ hc hu B.val)
      (fun v f => Subtype.ext (FrameTransport.Construction.quadratic_heisenberg ψ B v f.val)), rfl⟩

include hF hc hu hn in
theorem circleProjection_surjective [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) :
    Function.Surjective (Oscillator.Construction.circleProjection σ H K c ψ) := by
  by_cases h : ∀ k : ℕ, ‖(k : F)‖ ≤ 1
  · let : IsUltrametricDist F :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    exact UltraSurjectivity.Construction.circleProjection_surjective_ultra σ H K c ψ hF hc hu hn
  · obtain ⟨e, he, hei⟩ := ArchimedeanBase.Construction.real_equiv_of_unbounded_with_quadratic_extension h hQuadratic
    exact circleProjection_surjective_archimedean σ H K c hF ψ hc hu hn e he hei

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Surjectivity.Construction
