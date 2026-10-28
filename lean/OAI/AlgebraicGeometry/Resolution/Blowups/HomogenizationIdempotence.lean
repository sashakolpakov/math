import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedDifferentialStability

/-! # Homogenization Idempotence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationIdempotence.Construction

noncomputable section

/-! Tangent stability and idempotence of relative homogenization. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeHomogenizedIdeal_mono {J L : Ideal R} (h : J ≤ L) (n : ℕ) :
    Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n := by
  apply iSup_mono
  intro j
  exact Ideal.mul_mono (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k j.val h)
    (pow_le_pow_left' (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n h) j.val)

/-- One derivative of the homogenized ideal, multiplied by any tangent-ideal
section, stays in the homogenized ideal. -/
theorem relativeHomogenizedIdeal_first_stable (J : Ideal R) (n : ℕ) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) *
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) * T ≤ _
  conv_lhs => unfold Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal
  rw [Relative.DifferentialProducts.Construction.firstRelativeDifferentialIdeal_iSup, Ideal.iSup_mul]
  apply iSup_le
  intro j
  by_cases hj : j.val = n
  · rw [hj]
    change Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (T * T ^ n) * T ≤ _
    rw [← pow_succ']
    have hd : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (T ^ (n + 1)) ≤ T ^ n :=
      (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal_le_ordinary k (T ^ (n + 1))).trans
        (DifferentialIdealTransform.Construction.firstDifferentialIdeal_le_pow T (T ^ (n + 1)) n le_rfl)
    have h := Ideal.mul_mono hd (le_refl T)
    rw [← pow_succ] at h
    exact h.trans (Relative.DifferentialEquiv.Construction.tangentIdeal_power_le_relativeHomogenizedIdeal k J n)
  · have hjn : j.val + 1 ≤ n := by omega
    have he : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) =
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (j.val + 1) := by
      simpa only [Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal] using
        (Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_add k J j.val 1).symm
    have hnext : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) * T ^ (j.val + 1) ≤
          Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
      rw [he]
      exact HomogenizationTangent.Construction.relativeHomogenizedIdeal_component k J n (j.val + 1) hjn
    cases hjval : j.val with
    | zero =>
      simpa only [hjval, pow_zero, mul_one, zero_add, pow_one] using hnext
    | succ r =>
      have hstep := Ideal.mul_mono
        (Relative.DifferentialProducts.Construction.firstRelativeDifferentialIdeal_product_power_le k
          (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) T r) (le_refl T)
      rw [Ideal.sup_mul, mul_assoc, mul_assoc, ← pow_succ, ← pow_succ] at hstep
      have hcur : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val * T ^ j.val ≤
          Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n :=
        HomogenizationTangent.Construction.relativeHomogenizedIdeal_component k J n j.val (Nat.le_of_lt_succ j.isLt)
      rw [hjval] at hnext hcur hstep
      exact hstep.trans (sup_le hnext hcur)

/-- Homogenization is unchanged if performed a second time. -/
theorem relativeHomogenizedIdeal_idempotent (J : Ideal R) (n : ℕ) :
    Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n =
      Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
  apply le_antisymm
  · change (⨆ j : Fin (n + 1),
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) j.val *
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n) ^ j.val) ≤
          Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
    rw [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
    apply iSup_le
    intro j
    exact WeightedDifferentialStability.Construction.iteratedRelativeDifferential_weighted_stability k
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
      (relativeHomogenizedIdeal_first_stable k J n) j.val
  · exact Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n

theorem relativeHomogenizedIdeal_interval_eq (J L : Ideal R) (n : ℕ)
    (hJL : J ≤ L) (hLH : L ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) :
    Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n = Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
  apply le_antisymm
  · have h := relativeHomogenizedIdeal_mono k hLH n
    rwa [relativeHomogenizedIdeal_idempotent] at h
  · exact relativeHomogenizedIdeal_mono k hJL n

/-- Mutual comparison with homogenization is equivalent to exact equality
of the homogenized ideals. -/
theorem relativeHomogenizedIdeal_eq_iff (J L : Ideal R) (n : ℕ) :
    Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n = Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n ↔
      J ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k L n ∧ L ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
  constructor
  · intro h
    constructor
    · rw [← h]
      exact Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n
    · rw [h]
      exact Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k L n
  · rintro ⟨hJL, hLJ⟩
    apply le_antisymm
    · have h := relativeHomogenizedIdeal_mono k hJL n
      rwa [relativeHomogenizedIdeal_idempotent] at h
    · have h := relativeHomogenizedIdeal_mono k hLJ n
      rwa [relativeHomogenizedIdeal_idempotent] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationIdempotence.Construction
