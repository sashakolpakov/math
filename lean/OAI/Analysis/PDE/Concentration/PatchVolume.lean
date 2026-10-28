import OAI.Analysis.PDE.Concentration.FiberVolume

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Green

theorem physical_patch_volume_change {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) {P : Set (Option (Fin d) → ℂ)}
    (hP : MeasurableSet P) (hsub : P ⊆ OAI.Analysis.Calculus.Current.fiberParameterBall d) :
    volume.real (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ '' P) =
      ∫ u in P, |OAI.Analysis.Calculus.Current.physicalInverseJacobian a τ u| := by
  have hd : ∀ u ∈ P, HasFDerivWithinAt (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ)
      (fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ) u) P u := by
    intro u hu
    exact (((OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ u
      (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator (hsub hu))).restrict_scalars ℝ).differentiableAt
        (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume hP hd
    ((OAI.Analysis.PDE.Green.physicalFiberInverse_injOn_parameter_ball a τ ha ht).mono hsub) (fun _ => (1 : ℝ))
  simpa only [OAI.Analysis.Calculus.Current.physicalInverseJacobian, smul_eq_mul, mul_one, integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul] using he

/-- Actual physical volume of any compact parameter patch is bounded below
by its parameter volume times `a^(2N)`, uniformly for `a≤|τ|≤4a`. -/
theorem physical_patch_volume_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ), 0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a →
      ∀ (P : Set (Option (Fin d) → ℂ)), IsCompact P → P ⊆ OAI.Analysis.Calculus.Current.fiberParameterBall d →
      c * a ^ (2 * (d + 1)) * volume.real P ≤ volume.real (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ '' P) := by
  obtain ⟨c, C, hc, hC, hb⟩ := OAI.Analysis.Calculus.Current.physicalInverseJacobian_small_time_bounds d
  refine ⟨c, hc, ?_⟩
  intro a τ ha ht ht' P hP hsub
  rw [physical_patch_volume_change a τ ha ht hP.measurableSet hsub]
  have hcont : ContinuousOn (fun u => |OAI.Analysis.Calculus.Current.physicalInverseJacobian a τ u|) P := by
    intro u hu
    exact ((OAI.Analysis.Calculus.Current.continuousAt_physicalInverseJacobian a τ u (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator (hsub hu))).comp
      (continuous_const.prodMk continuous_id).continuousAt).abs.continuousWithinAt
  have hi := hcont.integrableOn_compact (μ := volume) hP
  have hle := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => mul_nonneg hc.le (pow_nonneg ha.le _)) hi
    (by
      filter_upwards [ae_restrict_mem hP.measurableSet] with u hu
      exact (hb a τ u ha ht ht' (hsub hu)).1)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using hle

/-- A rectangular subpatch of the manuscript's output patch. Its transverse
radius is at most `γ`, and its volume has the required `γ^(2d)` scale. -/
def outputParameterPatch (d : ℕ) (γ : ℝ) : Set (Option (Fin d) → ℂ) :=
  Set.pi univ (fun i => Metric.closedBall 0 (i.elim (1 / 400) (fun _ => γ / (d + 1))))

theorem outputParameterPatch_mem {d : ℕ} {γ : ℝ} {u : Option (Fin d) → ℂ} :
    u ∈ outputParameterPatch d γ ↔
      ‖u none‖ ≤ 1 / 400 ∧ ∀ i, ‖u (some i)‖ ≤ γ / (d + 1) := by
  simp only [outputParameterPatch, Set.mem_pi, Set.mem_univ, forall_const,
    Option.forall, Metric.mem_closedBall, dist_zero_right, Option.elim]

theorem isCompact_outputParameterPatch (d : ℕ) (γ : ℝ) :
    IsCompact (outputParameterPatch d γ) := isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem outputParameterPatch_transverse_bound {d : ℕ} {γ : ℝ} (_ : 0 ≤ γ)
    {u : Option (Fin d) → ℂ} (hu : u ∈ outputParameterPatch d γ) :
    (∑ i : Fin d, ‖u (some i)‖ ^ 2) ≤ γ ^ 2 := by
  have hb := (outputParameterPatch_mem.mp hu).2
  have hs : (∑ i : Fin d, ‖u (some i)‖ ^ 2) ≤ (d : ℝ) * (γ / (d + 1)) ^ 2 := by
    have he := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using he
  apply hs.trans
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) + 1) ^ 2)).mpr
  have hd : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hd (sq_nonneg γ)

theorem outputParameterPatch_subset {d : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 100) :
    outputParameterPatch d γ ⊆ OAI.Analysis.PDE.Green.openFiberParameterBall d := by
  intro u hu
  have hn := (outputParameterPatch_mem.mp hu).1
  have ht := outputParameterPatch_transverse_bound hγ hu
  change (∑ i, ‖u i‖ ^ 2) < (1 / 100 : ℝ)
  rw [Fintype.sum_option]
  nlinarith [norm_nonneg (u none)]

theorem outputParameterPatch_volume (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    volume.real (outputParameterPatch d γ) =
      ((1 / 400 : ℝ) ^ 2 * Real.pi) * ((γ / (d + 1)) ^ 2 * Real.pi) ^ d := by
  unfold Measure.real outputParameterPatch
  rw [volume_pi_pi, Fintype.prod_option]
  simp only [Complex.volume_closedBall, Option.elim, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 400),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ γ / ((d : ℝ) + 1))]
  rfl

theorem outputParameterPatch_volume_scale (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    volume.real (outputParameterPatch d γ) =
      ((1 / 400 : ℝ) ^ 2 * Real.pi * (Real.pi / (d + 1) ^ 2) ^ d) * γ ^ (2 * d) := by
  rw [outputParameterPatch_volume d hγ]
  have he : ((γ / (d + 1)) ^ 2 * Real.pi) ^ d =
      γ ^ (2 * d) * (Real.pi / (d + 1) ^ 2) ^ d := by
    rw [show (γ / (d + 1)) ^ 2 * Real.pi = γ ^ 2 * (Real.pi / (d + 1) ^ 2) by rw [div_pow]; ring,
      mul_pow, ← pow_mul]
  rw [he]
  ring

def physicalOutputPatch {d : ℕ} (a : ℝ) (τ : ℂ) (γ : ℝ) : Set (Option (Fin d) → ℂ) :=
  OAI.Analysis.Calculus.Current.physicalFiberInverse a τ '' outputParameterPatch d γ

theorem physicalOutputPatch_subset {d : ℕ} (a : ℝ) (τ : ℂ) (γ : ℝ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 100) :
    physicalOutputPatch (d := d) a τ γ ⊆ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} := by
  rw [← OAI.Analysis.PDE.Green.physicalFiberInverse_image_open_ball a τ ha ht]
  exact Set.image_mono (outputParameterPatch_subset hγ hγ1)

/-- The full physical output patch has the required lower volume
`a^(2N) γ^(2(N-1))`. Its exact inverse Jacobian is included. -/
theorem physicalOutputPatch_volume_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (γ : ℝ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → 0 ≤ γ → γ ≤ 1 / 100 →
      c * a ^ (2 * (d + 1)) * γ ^ (2 * d) ≤ volume.real (physicalOutputPatch (d := d) a τ γ) := by
  obtain ⟨c, hc, hb⟩ := physical_patch_volume_lower d
  let v : ℝ := (1 / 400 : ℝ) ^ 2 * Real.pi * (Real.pi / (d + 1) ^ 2) ^ d
  have hv : 0 < v := by dsimp only [v]; positivity
  refine ⟨c * v, mul_pos hc hv, ?_⟩
  intro a τ γ ha ht ht' hγ hγ1
  have hh := hb a τ ha ht ht' (outputParameterPatch d γ) (isCompact_outputParameterPatch d γ)
    ((outputParameterPatch_subset hγ hγ1).trans (OAI.Analysis.PDE.Green.openFiberParameterBall_subset d))
  rw [outputParameterPatch_volume_scale d hγ] at hh
  change c * a ^ (2 * (d + 1)) * (v * γ ^ (2 * d)) ≤ _ at hh
  calc
    _ = c * a ^ (2 * (d + 1)) * (v * γ ^ (2 * d)) := by ring
    _ ≤ _ := hh

theorem output_patch_scale (d : ℕ) (h : ℝ) {L : ℝ} (hL : 0 < L) :
    (h * L) ^ (2 * (d + 1)) * ((Real.sqrt L)⁻¹) ^ (2 * d) =
      h ^ (2 * (d + 1)) * L ^ (d + 2) := by
  rw [mul_pow, inv_pow, pow_mul (Real.sqrt L) 2 d, Real.sq_sqrt hL.le]
  rw [show 2 * (d + 1) = d + (d + 2) by omega, pow_add]
  field_simp
  rw [pow_add]
  ring

theorem physicalOutputPatch_volume_semiclassical (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (h L : ℝ) (τ : ℂ), 0 < h → 10000 ≤ L →
      h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      c * h ^ (2 * (d + 1)) * L ^ (d + 2) ≤
        volume.real (physicalOutputPatch (d := d) (h * L) τ (Real.sqrt L)⁻¹) := by
  obtain ⟨c, hc, hb⟩ := physicalOutputPatch_volume_lower d
  refine ⟨c, hc, ?_⟩
  intro h L τ hh hL ht ht'
  have hL0 : 0 < L := by linarith
  have hs : 100 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]
    norm_num
    linarith
  have hγ : (Real.sqrt L)⁻¹ ≤ (1 / 100 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hs
  have ho := hb (h * L) τ (Real.sqrt L)⁻¹ (mul_pos hh hL0) ht ht'
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) hγ
  rw [mul_assoc c, output_patch_scale d h hL0, ← mul_assoc] at ho
  exact ho

end OAI.Analysis.PDE.Concentration
