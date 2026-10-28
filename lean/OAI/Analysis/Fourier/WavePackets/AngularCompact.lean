import OAI.Analysis.Fourier.WavePackets.AngularGeometry

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped ContDiff ENNReal FourierTransform

theorem eLpNorm_fourierInv_comp_smooth {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (R : Space n ≃L[ℝ] Space n) :
    eLpNorm (𝓕⁻ (φ ∘ R)) 1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  apply eLpNorm_fourierInv_comp_linearEquiv R φ
  have he : ((𝓕⁻ (hc.toSchwartzMap hφ) : SchwartzMap (Space n) ℂ) : Space n → ℂ) =
      𝓕⁻ φ := by rw [SchwartzMap.fourierInv_coe]; rfl
  rw [← he]
  exact (𝓕⁻ (hc.toSchwartzMap hφ)).continuous.measurable

theorem finite_positive_lower_bound {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ a i := by
  classical
  have h (s : Finset ι) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ a i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hεs⟩ := ih
      refine ⟨min ε (a i), lt_min hε (ha i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεs j hjs)
  obtain ⟨ε, hε, hεall⟩ := h Finset.univ
  exact ⟨ε, hε, fun i => hεall i (Finset.mem_univ i)⟩

/-- One fixed compact packet-frequency set will contain all the rotated
grid sectors, independently of the grid scale. -/
def angularPacketCompact (d : ℕ) (ε B : ℝ) : Set (OAI.Analysis.Calculus.Current.SpatialSpace d) :=
  {η | ‖η‖ ≤ B ∧ ε ≤ η none ∧
    ‖OAI.Analysis.PDE.Concentration.transverseFrequency η‖ ≤ OAI.Analysis.PDE.Concentration.gaussianFrequencyK η / 40}

theorem isCompact_angularPacketCompact (d : ℕ) (ε B : ℝ) :
    IsCompact (angularPacketCompact d ε B) := by
  apply (isCompact_closedBall (0 : OAI.Analysis.Calculus.Current.SpatialSpace d) B).of_isClosed_subset
  · exact (isClosed_le continuous_norm continuous_const).inter
      ((isClosed_le continuous_const (EuclideanSpace.proj none).continuous).inter
        (isClosed_le (OAI.Analysis.PDE.Concentration.transverseFrequency.continuous.norm)
          (OAI.Analysis.PDE.Concentration.continuous_gaussianFrequencyK.div_const 40)))
  · intro η hη
    simpa only [Metric.mem_closedBall, dist_zero_right] using hη.1

theorem angularPacketCompact_positive {d : ℕ} {ε B : ℝ} (hε : 0 < ε)
    {η : OAI.Analysis.Calculus.Current.SpatialSpace d} (hη : η ∈ angularPacketCompact d ε B) :
    0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η := by
  change 0 < (η none + ‖η‖) / Real.sqrt 2
  exact div_pos (add_pos_of_pos_of_nonneg (hε.trans_le hη.2.1) (norm_nonneg _)) (by positivity)

theorem angularPacketCompact_velocity {d : ℕ} {ε B : ℝ} (hε : 0 < ε)
    {η : OAI.Analysis.Calculus.Current.SpatialSpace d} (hη : η ∈ angularPacketCompact d ε B) :
    ‖OAI.Analysis.PDE.Concentration.gaussianVelocity η‖ ≤ 1 / 40 := by
  have hk := angularPacketCompact_positive hε hη
  rw [OAI.Analysis.PDE.Concentration.gaussianVelocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk),
    ← div_eq_inv_mul]
  apply (div_le_iff₀ hk).mpr
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hη.2.2

theorem mem_angularPacketCompact {d : ℕ} {ε B : ℝ} {η : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hB : ‖η‖ ≤ B) (hε : ε ≤ η none) (hk : 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η)
    (hv : ‖OAI.Analysis.PDE.Concentration.gaussianVelocity η‖ ≤ 1 / 40) :
    η ∈ angularPacketCompact d ε B := by
  refine ⟨hB, hε, ?_⟩
  rw [OAI.Analysis.PDE.Concentration.gaussianVelocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk),
    ← div_eq_inv_mul] at hv
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using (div_le_iff₀ hk).mp hv

end OAI.Analysis.Fourier.WavePackets
