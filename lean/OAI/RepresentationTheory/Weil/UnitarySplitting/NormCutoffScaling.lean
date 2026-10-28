import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterCutoffs

/-! # Norm Cutoff Scaling -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormCutoffScaling.Construction

noncomputable section

/-! Exact finite-cutoff quadratic-character scaling for the norm phase. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [CharZero F]
variable [IsUltrametricDist F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hne hω in
theorem norm_character_cutoff_scaling
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (t : F) (ht : ψ t ≠ 1) (r : ℝ) (hr : ‖t‖ ≤ r) (a : Fˣ) :
    (FieldModulus.Construction.fieldModulus F a : ℂ) *
        (∫ b, (Metric.closedBall (0 : F) r).indicator (fun x => ψ x)
          ((a : F) * Algebra.norm F b) ∂μE) =
      (ω a : ℂ) * (∫ b, (Metric.closedBall (0 : F) r).indicator (fun x => ψ x)
        (Algebra.norm F b) ∂μE) := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  have hfm : StronglyMeasurable ((Metric.closedBall (0 : F) r).indicator (fun x => ψ x)) :=
    hc.stronglyMeasurable.indicator measurableSet_closedBall
  have hf : Integrable ((Metric.closedBall (0 : F) r).indicator (fun x => ψ x)) μF :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
  exact NormQuadraticIntegrals.Construction.norm_test_integral_scaling hF hE hEmbedding hQuadratic σ hne ω hω μF μE _ hfm hf
    (CharacterCutoffs.Construction.ultra_character_closedBall_integral_zero μF ψ t ht r hr) a

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormCutoffScaling.Construction
