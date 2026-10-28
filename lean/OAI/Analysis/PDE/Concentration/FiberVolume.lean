import OAI.Analysis.PDE.Green.Physical.Change
import OAI.Analysis.Calculus.Current.Physical.Volume

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green

theorem openFiberParameterBall_finite (d : ℕ) :
    volume (OAI.Analysis.PDE.Green.openFiberParameterBall d) ≠ ⊤ :=
  ne_top_of_le_ne_top (OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d).measure_ne_top
    (measure_mono (OAI.Analysis.PDE.Green.openFiberParameterBall_subset d))

theorem physical_imaginary_fiber_finite {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    volume {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} ≠ ⊤ := by
  have hc : ContinuousOn (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ) (OAI.Analysis.Calculus.Current.fiberParameterBall d) := by
    intro u hu
    exact (OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ u
      (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)).continuousAt.continuousWithinAt
  rw [← OAI.Analysis.PDE.Green.physicalFiberInverse_image_open_ball a τ ha ht]
  exact ne_top_of_le_ne_top ((OAI.Analysis.Calculus.Current.isCompact_fiberParameterBall d).image_of_continuousOn hc).measure_ne_top
    (measure_mono (image_mono (OAI.Analysis.PDE.Green.openFiberParameterBall_subset d)))

/-- At small times the actual imaginary fiber has real volume of order at most
`a^(2(d+1))`. The domain here is the physical rational sublevel, not the
normalized parameter ball. -/
theorem physical_imaginary_fiber_volume_upper (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (τ : ℂ), 0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a →
      volume.real {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} ≤
        C * a ^ (2 * (d + 1)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := OAI.Analysis.Calculus.Current.physicalInverseJacobian_small_time_bounds d
  refine ⟨C * (volume.real (OAI.Analysis.PDE.Green.openFiberParameterBall d) + 1), by positivity, ?_⟩
  intro a τ ha ht ht'
  let : IsFiniteMeasure (volume.restrict (OAI.Analysis.PDE.Green.openFiberParameterBall d)) :=
    isFiniteMeasure_restrict.mpr (openFiberParameterBall_finite d)
  have he := OAI.Analysis.PDE.Green.physical_fiber_integral_change (d := d) a τ ha ht (fun _ => (1 : ℝ))
  simp only [mul_one, integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at he
  rw [he]
  have hle : (∫ u in OAI.Analysis.PDE.Green.openFiberParameterBall d, |OAI.Analysis.Calculus.Current.physicalInverseJacobian a τ u|) ≤
      ∫ _u in OAI.Analysis.PDE.Green.openFiberParameterBall d, C * a ^ (2 * (d + 1)) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (integrable_const _)
    filter_upwards [ae_restrict_mem (OAI.Analysis.PDE.Green.isOpen_openFiberParameterBall d).measurableSet] with u hu
    exact (hb a τ u ha ht ht' (OAI.Analysis.PDE.Green.openFiberParameterBall_subset d hu)).2
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hle
  exact hle.trans (by nlinarith [pow_nonneg ha.le (2 * (d + 1))])

end OAI.Analysis.PDE.Concentration
