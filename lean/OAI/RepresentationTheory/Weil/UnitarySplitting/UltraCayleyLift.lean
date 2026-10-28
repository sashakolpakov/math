import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraSurjectivity

/-! # Ultra Cayley Lift -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyLift.Construction

noncomputable section

/-! Positive normalization places the canonical Cayley operator in the
actual trace-tensor circle extension. -/

open _root_.MeasureTheory

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F]
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)

theorem frameLift_heisenberg_covariance
    (g : FrameTransport.Construction.StandardSymplectic F (m * n)) (a : Oscillator.Construction.CircleExtension σ H K c ψ)
    (ha : Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c g)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
    a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g.val v) (a.val.2 f) := by
  have hh := (a.property.2 (c.coordinates.symm v) f (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)).mp
    (by rw [c.coordinates.apply_symm_apply]; rfl)
  have ha' : a.val.1 = FrameTransport.Construction.frameSymplectic σ H K c g := ha
  change (a.val.2 (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)).val =
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (c.coordinates (a.val.1.val (c.coordinates.symm v))) (a.val.2 f).val at hh
  rw [ha', FrameTransport.Construction.frameSymplectic_coordinates, c.coordinates.apply_symm_apply] at hh
  exact Subtype.ext hh

variable [IsUltrametricDist F] [SecondCountableTopology F]
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
variable (g : FrameTransport.Construction.StandardSymplectic F (m * n))
variable (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
variable (hD : ∀ x, D x = g.val x - x)

theorem exists_ultraCayleyLift :
    ∃ (r : ℝ) (a : Oscillator.Construction.CircleExtension σ H K c ψ), 0 < r ∧
      Oscillator.Construction.circleProjection σ H K c ψ a = FrameTransport.Construction.frameSymplectic σ H K c g ∧
      ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n),
        UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f = (r : ℂ) • a.val.2 f := by
  obtain ⟨b, hb⟩ := UltraSurjectivity.Construction.circleProjection_surjective_ultra σ H K c ψ hF hc hu hn
    (FrameTransport.Construction.frameSymplectic σ H K c g)
  obtain ⟨r, V, hr, hM, henergy, hcov⟩ := UltraIntertwinerNormalization.Construction.ultraIntertwiner_positive_normalization hF ψ hc hu hn
    g.val (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD)
    (UltraCayleyOperator.Construction.ultraCayleyOperator_ne_zero hF ψ hc hu hn ν g D hD)
    (UltraCayleyOperator.Construction.ultraCayleyOperator_intertwines hF ψ hc hu hn ν g D hD) b.val.2
    (frameLift_heisenberg_covariance σ H K c hF ψ hc hu g b hb) b.property.1
  exact ⟨r, FrameTransport.Construction.frameOscillatorLift σ H K c hF ψ hc hu g V henergy hcov, hr, rfl, hM⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyLift.Construction
