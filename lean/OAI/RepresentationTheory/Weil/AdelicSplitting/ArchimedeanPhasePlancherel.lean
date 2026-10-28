import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterScalingSq
import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.RapidFunctions

/-! # Archimedean Phase Plancherel -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Plancherel for continuous rapidly decreasing phase-space amplitudes,
including a continuous unit-modulus multiplier. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier.Construction _root_.MeasureTheory

def RapidFunctions.LocalAnalysis.RapidFunction.unitPhase {V : Type*} [NormedAddCommGroup V]
    (f : RapidFunctions.LocalAnalysis.RapidFunction V) (a : V → ℂ) (ha : Continuous a) (hu : ∀ x, ‖a x‖ = 1) : RapidFunctions.LocalAnalysis.RapidFunction V where
  toContinuousMap := ⟨fun x => a x * f x, ha.mul f.continuous⟩
  decay j := by
    obtain ⟨C, hC, hb⟩ := f.decay j
    refine ⟨C, hC, fun x => ?_⟩
    change (1 + ‖x‖) ^ j * ‖a x * f x‖ ≤ C
    simpa only [norm_mul, hu, one_mul] using hb x

theorem RapidFunctions.LocalAnalysis.RapidFunction.memLp_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (f : RapidFunctions.LocalAnalysis.RapidFunction V) (μ : Measure V) [μ.IsAddHaarMeasure] : MemLp f 2 μ := by
  obtain ⟨C, -, hb⟩ := f.decay 0
  have hbound (x : V) : ‖f x‖ ≤ C := by simpa only [pow_zero, one_mul] using hb x
  apply (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mpr
  apply ((f.integrable μ).norm.mul_const C).mono'
    (f.continuous.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change ‖‖f x‖ ^ 2‖ ≤ ‖f x‖ * C
    rw [norm_pow, norm_norm, pow_two]
    exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)

theorem ArchimedeanPhasePlancherel.LocalAnalysis.real_phaseFourier_rapid_energy {N : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ N)) :
    (∫ v, ‖∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing ℝ N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)) =
      ∫ v, ‖f v‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
    (RealNormalization.LocalAnalysis.real_fourier_analysis (N + N) ψ hc hu hn).1
  let a := f.compLinearEquiv (PhaseMeasure.Construction.phaseCoordinates ℝ N).symm
  exact PhaseFourier.Construction.phaseFourier_norm_sq_of_coordinate ℝ N ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ) f
    (CharacterScalingSq.LocalAnalysis.real_fourier_L2_normalized ψ hc hu hn (a.integrable volume) (a.memLp_two volume))

theorem ArchimedeanPhasePlancherel.LocalAnalysis.complex_phaseFourier_rapid_energy {N : ℕ} (ψ : AddChar ℂ ℂ)
    (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : RapidFunctions.LocalAnalysis.RapidFunction (Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N)) :
    (∫ v, ‖∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing ℂ N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ)) =
      ∫ v, ‖f v‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) := by
  let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ
    (ComplexNormalization.LocalAnalysis.complex_fourier_analysis (N + N) ψ hc hu hn).1
  let e : Local.FunctionsMetaplectic.Construction.Position ℂ (N + N) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℂ N :=
    { __ := (PhaseMeasure.Construction.phaseCoordinates ℂ N).symm.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (PhaseMeasure.Construction.phaseCoordinates ℂ N).symm.continuous
      continuous_invFun := (PhaseMeasure.Construction.phaseCoordinates ℂ N).continuous }
  let a := f.compLinearEquiv e
  exact PhaseFourier.Construction.phaseFourier_norm_sq_of_coordinate ℂ N ψ (Local.FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) f
    (CharacterScalingSq.LocalAnalysis.complex_fourier_L2_normalized ψ hc hu hn (a.integrable volume) (a.memLp_two volume))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
