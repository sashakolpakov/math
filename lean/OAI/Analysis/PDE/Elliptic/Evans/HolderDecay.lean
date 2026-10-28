import OAI.Analysis.PDE.Elliptic.Evans.GeometricIteration

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- A monotone oscillation with a strict contraction and linear error has
a uniform positive Hölder exponent. -/
theorem holder_decay_of_oscillation_contraction {ρ θ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C > 0, ∀ ω : ℝ → ℝ, ω 1 ≤ A →
        (∀ r s, 0 < r → r ≤ s → s ≤ 1 → ω r ≤ ω s) →
        (∀ r, 0 < r → r ≤ 1 → ω (ρ * r) ≤ θ * ω r + B * r) →
        ∀ r, 0 < r → r ≤ 1 → ω r ≤ C * r ^ α := by
  obtain ⟨α, hα, hα1, hgap⟩ := exists_oscillation_exponent hρ hρ1 hθ1
  let q := ρ ^ α
  have hq : 0 < q := Real.rpow_pos_of_pos hρ _
  have hρq : ρ ≤ q := (le_max_left _ _).trans hgap.le
  have hθq : θ < q := (le_max_right _ _).trans_lt hgap
  refine ⟨α, hα, hα1, ?_⟩
  intro A B hA hB
  let D := A + B / (q - θ) + 1
  have hdiv : 0 ≤ B / (q - θ) := div_nonneg hB (sub_nonneg.mpr hθq.le)
  have hD : 0 < D := by dsimp [D]; linarith
  have hAD : A ≤ D := by dsimp [D]; linarith
  have hBD : B ≤ D * (q - θ) := (div_le_iff₀ (sub_pos.mpr hθq)).mp (by
    dsimp [D]
    linarith)
  have hsize : θ * D + B ≤ D * q := by nlinarith
  refine ⟨D / q, div_pos hD hq, ?_⟩
  intro ω hstart hmono hstep
  have hseq : ∀ k : ℕ, ω (ρ ^ k) ≤ D * q ^ k := by
    apply geometric_inhomogeneous_bound hρ.le hρq hθ hB hsize
      (fun k ↦ ω (ρ ^ k))
    · simpa using hstart.trans hAD
    · intro k
      have hs := hstep (ρ ^ k) (pow_pos hρ k) (pow_le_one₀ hρ.le hρ1.le)
      simpa only [pow_succ, mul_comm (ρ ^ k) ρ] using hs
  have hpowers (k : ℕ) : (ρ ^ k) ^ α = q ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Real.mul_rpow (pow_nonneg hρ.le k) hρ.le, ih, pow_succ]
  intro r hr hr1
  obtain ⟨k, hklo, hkhi⟩ := exists_geometric_radius hρ hρ1 hr hr1
  have hpow : q ^ k * q ≤ r ^ α := by
    have h := Real.rpow_le_rpow (pow_nonneg hρ.le (k + 1)) hklo.le hα.le
    rwa [hpowers, pow_succ] at h
  calc
    ω r ≤ ω (ρ ^ k) := hmono r (ρ ^ k) hr hkhi (pow_le_one₀ hρ.le hρ1.le)
    _ ≤ D * q ^ k := hseq k
    _ ≤ D * (r ^ α / q) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hq).mpr hpow) hD.le
    _ = (D / q) * r ^ α := by ring

end OAI.Analysis.PDE.Elliptic
