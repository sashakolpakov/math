import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergy
import OAI.RepresentationTheory.Weil.UnitarySplitting.EnergyIntertwinerNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.Surjectivity
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyLift

/-! # Real Cayley Lift -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyLift.Construction

noncomputable section

/-! Canonical positive real Cayley lifts in the actual circle extension. -/

open _root_.MeasureTheory

variable {E : Type} [NormedField E] [Algebra ℝ E] {m n : ℕ}
variable (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))) [ν.IsAddHaarMeasure]
variable (g : FrameTransport.Construction.StandardSymplectic ℝ (m * n))
variable (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
variable (hD : ∀ x, D x = g.val x - x)

theorem exists_realCayleyLift :
    ∃ (r : ℝ) (a : Oscillator.Construction.CircleExtension σ H K c ψ), 0 < r ∧
      Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c g ∧
      ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n),
        RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f = (r : ℂ) • a.val.2 f := by
  obtain ⟨b, hb⟩ := Surjectivity.Construction.circleProjection_surjective_archimedean σ H K c RealFourierUnitary.Construction.real_nondiscrete ψ hc hu hn
    (RingEquiv.refl ℝ) continuous_id continuous_id (FrameTransport.Construction.frameSymplectic σ H K c g)
  obtain ⟨s, hs, hMs⟩ := RealCayleyEnergy.Construction.realCayleyOperator_energy_factor ψ hc hu hn ν g D hD
  obtain ⟨r, V, hr, hM, henergy, hcov⟩ := EnergyIntertwinerNormalization.Construction.energyIntertwiner_positive_normalization RealFourierUnitary.Construction.real_nondiscrete ψ hc hu hn
    g.val (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD)
    (RealCayleyOperator.Construction.realCayleyOperator_intertwines ψ hc hu hn ν g D hD) s hs hMs b.val.2
    (UltraCayleyLift.Construction.frameLift_heisenberg_covariance σ H K c RealFourierUnitary.Construction.real_nondiscrete ψ hc hu g b hb) b.property.1
  exact ⟨r, FrameTransport.Construction.frameOscillatorLift σ H K c RealFourierUnitary.Construction.real_nondiscrete ψ hc hu g V henergy hcov, hr, rfl, hM⟩

def realCayleyLiftRadius : ℝ :=
  Classical.choose (exists_realCayleyLift σ H K c ψ hc hu hn ν g D hD)

def realCayleyLift : Oscillator.Construction.CircleExtension σ H K c ψ :=
  Classical.choose (Classical.choose_spec (exists_realCayleyLift σ H K c ψ hc hu hn ν g D hD))

theorem realCayleyLift_spec :
    0 < realCayleyLiftRadius σ H K c ψ hc hu hn ν g D hD ∧
      Oscillator.Construction.circleProjection σ H K c ψ (realCayleyLift σ H K c ψ hc hu hn ν g D hD) = FrameTransport.Construction.frameSymplectic σ H K c g ∧
      ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n),
        RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f =
          (realCayleyLiftRadius σ H K c ψ hc hu hn ν g D hD : ℂ) •
            (realCayleyLift σ H K c ψ hc hu hn ν g D hD).val.2 f :=
  Classical.choose_spec (Classical.choose_spec (exists_realCayleyLift σ H K c ψ hc hu hn ν g D hD))

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyLift.Construction
