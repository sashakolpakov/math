import OAI.Analysis.PDE.Concentration.Lattice.Current

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped Matrix Matrix.Norms.Elementwise

theorem phaseArgument_add {d : ℕ} (L x y : OAI.Analysis.Calculus.Current.Index d → ℝ) :
    OAI.Analysis.Calculus.Current.phaseArgument L (x + y) = OAI.Analysis.Calculus.Current.phaseArgument L x + OAI.Analysis.Calculus.Current.phaseArgument L y := by
  simp [OAI.Analysis.Calculus.Current.phaseArgument, mul_add, Finset.sum_add_distrib]

/-- Phase quantization gives actual periodicity of each Fourier mode. -/
theorem phaseComplex_periodic_of_integer_phase {d : ℕ}
    (cR cI : ℝ) (L w : OAI.Analysis.Calculus.Current.Index d → ℝ) (k : ℤ)
    (hw : OAI.Analysis.Calculus.Current.phaseArgument L w = (k : ℝ) * (2 * Real.pi)) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) :
    OAI.Analysis.Calculus.Current.phaseComplex cR cI L (x + w) = OAI.Analysis.Calculus.Current.phaseComplex cR cI L x := by
  simp only [OAI.Analysis.Calculus.Current.phaseComplex, OAI.Analysis.Calculus.Current.phaseF, OAI.Analysis.Calculus.Current.phaseG, phaseArgument_add, hw,
    Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

theorem normalizedModeAmplitude_periodic {d : ℕ} (κ cR cI : ℝ)
    (v : Fin d → ℝ) (w : OAI.Analysis.Calculus.Current.Index d → ℝ) (k : ℤ)
    (hw : OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) w = (k : ℝ) * (2 * Real.pi))
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    OAI.Analysis.Calculus.Current.normalizedModeAmplitude κ cR cI v (x + w) z = OAI.Analysis.Calculus.Current.normalizedModeAmplitude κ cR cI v x z := by
  unfold OAI.Analysis.Calculus.Current.normalizedModeAmplitude OAI.Analysis.Calculus.Current.modeAmplitude
  rw [phaseComplex_periodic_of_integer_phase _ _ _ _ k hw]

theorem waveCurrent_periodic_of_integer_phases {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (w : OAI.Analysis.Calculus.Current.Index d → ℝ)
    (hw : ∀ j, ∃ k : ℤ, OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector (κ j) (v j)) w = (k : ℝ) * (2 * Real.pi))
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    OAI.Analysis.Calculus.Current.waveCurrent κ cR cI v (x + w) z = OAI.Analysis.Calculus.Current.waveCurrent κ cR cI v x z := by
  have hm (j : ι) : OAI.Analysis.Calculus.Current.normalizedModeAmplitude (κ j) (cR j) (cI j) (v j) (x + w) z =
      OAI.Analysis.Calculus.Current.normalizedModeAmplitude (κ j) (cR j) (cI j) (v j) x z := by
    obtain ⟨k, hk⟩ := hw j
    exact normalizedModeAmplitude_periodic _ _ _ _ _ k hk _ _
  simp only [OAI.Analysis.Calculus.Current.waveCurrent, hm]

theorem regularizedCurrent_periodic_of_integer_phases {d : ℕ} {ι α : Type*}
    [Fintype ι] [MeasurableSpace α] (μ : Measure α) (shift : α → OAI.Analysis.Calculus.Current.Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (w : OAI.Analysis.Calculus.Current.Index d → ℝ)
    (hw : ∀ j, ∃ k : ℤ, OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector (κ j) (v j)) w = (k : ℝ) * (2 * Real.pi))
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    OAI.Analysis.Calculus.Current.regularizedCurrent μ shift h a κ cR cI v (x + w) z =
      OAI.Analysis.Calculus.Current.regularizedCurrent μ shift h a κ cR cI v x z := by
  have he : OAI.Analysis.Calculus.Current.averagedWaveCurrent μ shift κ cR cI v (x + w) z =
      OAI.Analysis.Calculus.Current.averagedWaveCurrent μ shift κ cR cI v x z := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show x + w + shift t = (x + shift t) + w by abel]
    exact waveCurrent_periodic_of_integer_phases κ cR cI v w hw _ z
  simp only [OAI.Analysis.Calculus.Current.regularizedCurrent, OAI.Analysis.Calculus.Current.cutoffCurrent, he]

theorem latticeRegularizedCurrent_periodic {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (w : OAI.Analysis.Calculus.Current.Index d → ℝ)
    (hw : ∀ j, ∃ k : ℤ, OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector (κ j) (v j)) w = (k : ℝ) * (2 * Real.pi))
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) :
    latticeRegularizedCurrent R h a κ cR cI v (x + w) z =
      latticeRegularizedCurrent R h a κ cR cI v x z :=
  regularizedCurrent_periodic_of_integer_phases _ _ h a κ cR cI v w hw x z

end OAI.Analysis.PDE.Concentration
