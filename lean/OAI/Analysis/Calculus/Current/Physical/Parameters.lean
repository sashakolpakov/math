import OAI.Analysis.Calculus.Current.Physical.Inverse

/-! A fixed compact parameter ball for the physical fibers. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

def fiberParameterBall (d : ℕ) : Set (Option (Fin d) → ℂ) :=
  {u | (∑ i, ‖u i‖ ^ 2) ≤ (1 / 100 : ℝ)}

theorem fiberParameterBall_coordinate {d : ℕ} {u : Option (Fin d) → ℂ}
    (hu : u ∈ fiberParameterBall d) (i : Option (Fin d)) : ‖u i‖ ≤ (1 / 10 : ℝ) := by
  have hi : ‖u i‖ ^ 2 ≤ ∑ j, ‖u j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖u j‖) (Finset.mem_univ i)
  change (∑ j, ‖u j‖ ^ 2) ≤ (1 / 100 : ℝ) at hu
  nlinarith [norm_nonneg (u i)]

theorem fiberParameterBall_denominator {d : ℕ} {u : Option (Fin d) → ℂ}
    (hu : u ∈ fiberParameterBall d) : fiberDenominator (fun i => u (some i)) ≠ 0 := by
  apply fiberDenominator_ne_zero
  change (∑ j, ‖u j‖ ^ 2) ≤ (1 / 100 : ℝ) at hu
  rw [Fintype.sum_option] at hu
  nlinarith [sq_nonneg ‖u none‖]

theorem fiberParameterBall_numerator {d : ℕ} (a : ℝ) (τ : ℂ) (ha : 0 < a)
    (ht : a ≤ ‖τ‖) {u : Option (Fin d) → ℂ} (hu : u ∈ fiberParameterBall d) :
    Real.sqrt 2 • τ + a • u none ≠ 0 := by
  have hs : 1 ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  intro hz
  have he : Real.sqrt 2 • τ = -(a • u none) := eq_neg_of_add_eq_zero_left hz
  have hn := congrArg norm he
  rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos ha] at hn
  have hc := fiberParameterBall_coordinate hu none
  nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg τ)]

theorem isCompact_fiberParameterBall (d : ℕ) : IsCompact (fiberParameterBall d) := by
  have hp : Continuous (fun u : Option (Fin d) → ℂ => ∑ i, ‖u i‖ ^ 2) := by fun_prop
  have hc : IsClosed (fiberParameterBall d) := isClosed_le hp continuous_const
  apply (isCompact_closedBall (0 : Option (Fin d) → ℂ) 1).of_isClosed_subset hc
  intro u hu
  simp only [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  exact fun i => (fiberParameterBall_coordinate hu i).trans (by norm_num)

theorem fiberParameterBall_nonempty (d : ℕ) : (fiberParameterBall d).Nonempty :=
  ⟨0, by simp [fiberParameterBall]⟩

theorem physical_inverse_defining {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (ha : a ≠ 0)
    (hN : Real.sqrt 2 • τ + a • u none ≠ 0)
    (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    physicalFiberDefining (1 / 10) a τ (physicalFiberInverse a τ u) =
      100 * (∑ i, ‖u i‖ ^ 2) - 1 := by
  have he := physicalCoordinates_right_inverse a τ u ha hN hD
  have h0 := congrFun he none
  have hW (i : Fin d) := congrFun he (some i)
  change phi (physicalEmbedding τ (physicalFiberInverse a τ u)) / (a : ℂ) = u none at h0
  change ∀ i : Fin d, ratio (physicalEmbedding τ (physicalFiberInverse a τ u)) i = u (some i) at hW
  unfold physicalFiberDefining fiberDefining
  simp only [Fintype.sum_option, fiberMap, hW]
  have hc : 10 * phi (physicalEmbedding τ (physicalFiberInverse a τ u)) / (a : ℂ) = 10 * u none := by
    rw [mul_div_assoc, h0]
  rw [hc]
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, mul_pow, div_pow]
  norm_num
  rw [← Finset.sum_div]
  ring

theorem contDiffAt_physicalFiberInverse_joint {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContDiffAt ℂ ⊤ (fun p : ℂ × (Option (Fin d) → ℂ) => physicalFiberInverse a p.1 p.2) (τ, u) := by
  have hH : ContDiffAt ℂ ⊤ (fun p : ℂ × (Option (Fin d) → ℂ) => inverseHeight a p.1 p.2) (τ, u) := by
    unfold inverseHeight fiberDenominator fiberQuadratic
    simp only [Complex.real_smul]
    fun_prop (disch := exact hD)
  apply contDiffAt_pi.mpr
  intro b
  cases b with
  | none =>
    change ContDiffAt ℂ ⊤ (fun p : ℂ × (Option (Fin d) → ℂ) => Real.sqrt 2 • inverseHeight a p.1 p.2 - p.1) (τ, u)
    exact (hH.const_smul (Real.sqrt 2)).sub contDiffAt_fst
  | some i =>
    change ContDiffAt ℂ ⊤ (fun p : ℂ × (Option (Fin d) → ℂ) => p.2 (some i) * inverseHeight a p.1 p.2) (τ, u)
    exact (by fun_prop : ContDiffAt ℂ ⊤ (fun p : ℂ × (Option (Fin d) → ℂ) => p.2 (some i)) (τ, u)).mul hH

end OAI.Analysis.Calculus.Current
