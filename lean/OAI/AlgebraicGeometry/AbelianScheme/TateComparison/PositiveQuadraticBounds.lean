import Mathlib

/-! # Positive Quadratic Bounds -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveQuadraticBounds

noncomputable section

/-! A continuous positive quadratic function controls the ambient norm.
This gives bounded orbits for polarization-preserving lattice maps. -/

open _root_.Metric Bornology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem positiveQuadratic_norm_bound (Q : V → ℝ) (hc : Continuous Q)
    (hs : ∀ (a : ℝ) (x : V), Q (a • x) = a ^ 2 * Q x)
    (hp : ∀ x : V, x ≠ 0 → 0 < Q x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ Q x := by
  have hzero : Q 0 = 0 := by simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] using hs 0 0
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨1, zero_lt_one, fun x => by rw [Subsingleton.elim x 0, norm_zero, hzero]; norm_num⟩
  · obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
    have hvnorm : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hv
    have hvzero : v ≠ 0 := by
      intro hz
      exact zero_ne_one (by simpa only [hz, norm_zero] using hvnorm)
    refine ⟨Q v, hp v hvzero, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp only [hx, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, hzero, le_refl]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hu : ‖x‖⁻¹ • x ∈ sphere (0 : V) 1 := by
        simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn]
      have hm := hmin hu
      have he : Q x = ‖x‖ ^ 2 * Q (‖x‖⁻¹ • x) := by
        have hh := hs ‖x‖ (‖x‖⁻¹ • x)
        simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hh
      rw [he, mul_comm (Q v)]
      exact mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)

theorem positiveQuadratic_sublevel_bounded (Q : V → ℝ) (hc : Continuous Q)
    (hs : ∀ (a : ℝ) (x : V), Q (a • x) = a ^ 2 * Q x)
    (hp : ∀ x : V, x ≠ 0 → 0 < Q x) (r : ℝ) :
    IsBounded {x : V | Q x ≤ r} := by
  obtain ⟨c, hcpos, hbound⟩ := positiveQuadratic_norm_bound Q hc hs hp
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|r| / c + 1, ?_⟩
  intro x hx
  have hh : ‖x‖ ^ 2 ≤ |r| / c := by
    apply (le_div_iff₀ hcpos).mpr
    exact (mul_comm c (‖x‖ ^ 2) ▸ hbound x).trans (hx.trans (le_abs_self r))
  have hk : 0 ≤ |r| / c := div_nonneg (abs_nonneg r) hcpos.le
  nlinarith [sq_nonneg (‖x‖ - 1)]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PositiveQuadraticBounds
