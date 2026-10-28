import OAI.Analysis.Calculus.Current.Physical.Jacobian
import OAI.Analysis.Calculus.Current.Physical.Parameters

/-! Two-sided small-time bounds for the ordinary real-volume Jacobian. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

theorem continuousAt_physicalInverseJacobian {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContinuousAt (fun p : ℂ × (Option (Fin d) → ℂ) => physicalInverseJacobian a p.1 p.2) (τ, u) := by
  let E := Option (Fin d) → ℂ
  let P := ℂ × E
  have hj := (contDiffAt_physicalFiberInverse_joint a τ u hD).restrict_scalars ℝ
  have hf : ContDiffAt ℝ ⊤
      (Function.uncurry (fun (p : P) (v : E) => physicalFiberInverse a p.1 v)) ((τ, u), u) := by
    have hg : ContDiffAt ℝ ⊤ (fun v : P × E => (v.1.1, v.2)) ((τ, u), u) := by
      dsimp only [P, E]
      fun_prop
    simpa only [Function.comp_def, Function.uncurry] using! hj.comp ((τ, u), u) hg
  have hp : ContDiffAt ℝ 0
      (fun p : P => fderiv ℝ (physicalFiberInverse a p.1) p.2) (τ, u) :=
    hf.fderiv contDiffAt_snd (by norm_num)
  exact ContinuousLinearMap.continuous_det.continuousAt.comp hp.continuousAt

def normalizedInverseParameters (d : ℕ) : Set (ℂ × (Option (Fin d) → ℂ)) :=
  {τ : ℂ | 1 ≤ ‖τ‖ ∧ ‖τ‖ ≤ 4} ×ˢ fiberParameterBall d

theorem isCompact_normalizedInverseParameters (d : ℕ) :
    IsCompact (normalizedInverseParameters d) := by
  have hc : IsCompact {τ : ℂ | 1 ≤ ‖τ‖ ∧ ‖τ‖ ≤ 4} := by
    apply (isCompact_closedBall (0 : ℂ) 4).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    intro τ hτ
    simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖τ‖ ≤ 4 from hτ.2)
  exact hc.prod (isCompact_fiberParameterBall d)

theorem normalizedInverseParameters_nonempty (d : ℕ) :
    (normalizedInverseParameters d).Nonempty := by
  refine ⟨(1, 0), ?_, ?_⟩
  · norm_num
  · simp [fiberParameterBall]

theorem physicalInverseJacobian_normalized_bounds (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (τ : ℂ) (u : Option (Fin d) → ℂ),
      1 ≤ ‖τ‖ → ‖τ‖ ≤ 4 → u ∈ fiberParameterBall d →
      c ≤ |physicalInverseJacobian 1 τ u| ∧ |physicalInverseJacobian 1 τ u| ≤ C := by
  have hc : ContinuousOn
      (fun p : ℂ × (Option (Fin d) → ℂ) => |physicalInverseJacobian 1 p.1 p.2|)
      (normalizedInverseParameters d) := by
    intro p hp
    exact (continuousAt_physicalInverseJacobian 1 p.1 p.2
      (fiberParameterBall_denominator hp.2)).abs.continuousWithinAt
  have hpos (p : ℂ × (Option (Fin d) → ℂ)) (hp : p ∈ normalizedInverseParameters d) :
      0 < |physicalInverseJacobian 1 p.1 p.2| := by
    apply abs_pos.mpr
    exact physicalInverseJacobian_ne_zero 1 p.1 p.2 (by norm_num)
      (fiberParameterBall_numerator 1 p.1 (by norm_num) hp.1.1 hp.2)
      (fiberParameterBall_denominator hp.2)
  obtain ⟨p, hp, hmin⟩ := (isCompact_normalizedInverseParameters d).exists_isMinOn
    (normalizedInverseParameters_nonempty d) hc
  change ∀ q ∈ normalizedInverseParameters d,
    |physicalInverseJacobian 1 p.1 p.2| ≤ |physicalInverseJacobian 1 q.1 q.2| at hmin
  obtain ⟨B, hB⟩ := (isCompact_normalizedInverseParameters d).exists_bound_of_continuousOn hc
  refine ⟨|physicalInverseJacobian 1 p.1 p.2|, |B| + 1, hpos p hp, by positivity, ?_⟩
  intro τ u ht ht' hu
  have htu : (τ, u) ∈ normalizedInverseParameters d := ⟨⟨ht, ht'⟩, hu⟩
  constructor
  · exact hmin (τ, u) htu
  · have hb := hB (τ, u) htu
    simp only [Real.norm_eq_abs, abs_abs] at hb
    exact hb.trans (by linarith [le_abs_self B])

/-- Ordinary real volume in `(P,Z)` scales like `a^(2n)` relative to `(W,Φ/a)`. -/
theorem physicalInverseJacobian_small_time_bounds (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → u ∈ fiberParameterBall d →
      c * a ^ (2 * (d + 1)) ≤ |physicalInverseJacobian a τ u| ∧
      |physicalInverseJacobian a τ u| ≤ C * a ^ (2 * (d + 1)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := physicalInverseJacobian_normalized_bounds d
  refine ⟨c, C, hc, hC, ?_⟩
  intro a τ u ha ht ht' hu
  have hn : ‖a⁻¹ • τ‖ = ‖τ‖ / a := by
    simp [Real.norm_eq_abs, abs_of_pos ha, div_eq_mul_inv, mul_comm]
  have ht1 : 1 ≤ ‖a⁻¹ • τ‖ := by rw [hn]; exact (le_div_iff₀ ha).mpr (by simpa using ht)
  have ht4 : ‖a⁻¹ • τ‖ ≤ 4 := by rw [hn]; exact (div_le_iff₀ ha).mpr (by nlinarith)
  obtain ⟨hl, hu'⟩ := hb (a⁻¹ • τ) u ht1 ht4 hu
  have hs := physicalInverseJacobian_scale a (a⁻¹ • τ) u (fiberParameterBall_denominator hu)
  rw [smul_inv_smul₀ ha.ne'] at hs
  rw [hs, abs_mul, abs_of_pos (pow_pos ha _)]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (pow_nonneg ha.le _)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu' (pow_nonneg ha.le _)

end OAI.Analysis.Calculus.Current
