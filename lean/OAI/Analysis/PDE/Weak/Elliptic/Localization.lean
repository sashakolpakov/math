import OAI.Analysis.PDE.Weak.Elliptic.Coefficient
import OAI.Analysis.PDE.Weak.Elliptic.Derivative

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X) [μ.IsAddRightInvariant]

/-- The product rule with the cutoff on the unshifted difference quotient.
This form avoids any extra enlargement of the energy cutoff. -/
theorem differenceQuotientL2_cutoff (η : X → ℝ) (hη : Continuous η) {M L : ℝ}
    (hM : ∀ x, |η x| ≤ M) (v : X) (h : ℝ)
    (hL : ∀ x, |differenceQuotient v h η x| ≤ L) (u : Lp E 2 μ) :
    differenceQuotientL2 μ v h (cutoffL2 η hη hM u) =
      cutoffL2 η hη hM (differenceQuotientL2 μ v h u) +
        cutoffL2 (differenceQuotient v h η) (continuous_differenceQuotient v h hη)
          hL (translateL2 μ (h • v) u) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right μ (h • v)).quasiMeasurePreserving.ae
    (cutoffL2_ae η hη hM u)
  filter_upwards [coe_differenceQuotientL2 μ v h (cutoffL2 η hη hM u),
    cutoffL2_ae η hη hM u, ht,
    Lp.coeFn_add (cutoffL2 η hη hM (differenceQuotientL2 μ v h u))
      (cutoffL2 (differenceQuotient v h η) (continuous_differenceQuotient v h hη)
        hL (translateL2 μ (h • v) u)),
    cutoffL2_ae η hη hM (differenceQuotientL2 μ v h u),
    cutoffL2_ae (differenceQuotient v h η) (continuous_differenceQuotient v h hη)
      hL (translateL2 μ (h • v) u), coe_differenceQuotientL2 μ v h u,
    coe_translateL2 μ (h • v) u] with x hx hy hz hw ha hb hc hd
  rw [hx, hw]
  simp only [Pi.add_apply, ha, hb, hc, hd, differenceQuotient, hy, hz,
    smul_eq_mul]
  module

theorem norm_differenceQuotientL2_cutoff_le (η : X → ℝ) (hη : Continuous η) {M L : ℝ}
    (hM : ∀ x, |η x| ≤ M) (v : X) (h : ℝ)
    (hL : ∀ x, |differenceQuotient v h η x| ≤ L) (u : Lp E 2 μ) :
    ‖differenceQuotientL2 μ v h (cutoffL2 η hη hM u)‖ ≤
      ‖cutoffL2 η hη hM (differenceQuotientL2 μ v h u)‖ + L * ‖u‖ := by
  rw [differenceQuotientL2_cutoff μ η hη hM v h hL u]
  have hb := norm_cutoffL2_le (differenceQuotient v h η)
    (continuous_differenceQuotient v h hη) hL (translateL2 μ (h • v) u)
  rw [norm_translateL2] at hb
  exact (norm_add_le _ _).trans (add_le_add le_rfl hb)

variable [IsLocallyFiniteMeasure μ]

omit [NormedSpace ℝ X] [μ.IsAddRightInvariant] in
theorem integrable_cutoffL2 (η : X → ℝ) (hη : Continuous η)
    (hs : HasCompactSupport η) {M : ℝ} (hM : ∀ x, |η x| ≤ M) (u : Lp E 2 μ) :
    Integrable (cutoffL2 η hη hM u : X → E) μ := by
  have hu : IntegrableOn (cutoffL2 η hη hM u : X → E) (tsupport η) μ := by
    have : IsFiniteMeasure (μ.restrict (tsupport η)) :=
      ⟨by simpa using hs.isCompact.measure_lt_top (μ := μ)⟩
    exact ((Lp.memLp (cutoffL2 η hη hM u)).restrict (tsupport η)).integrable (by norm_num)
  have he : (cutoffL2 η hη hM u : X → E) =ᵐ[μ]
      (tsupport η).indicator (cutoffL2 η hη hM u : X → E) := by
    filter_upwards [cutoffL2_ae η hη hM u] with x hx
    by_cases hxs : x ∈ tsupport η
    · simp [hxs]
    · rw [indicator_of_notMem hxs, hx, image_eq_zero_of_notMem_tsupport hxs, zero_smul]
  exact (hu.integrable_indicator isClosed_closure.measurableSet).congr he.symm

end OAI.Analysis.PDE.Weak
