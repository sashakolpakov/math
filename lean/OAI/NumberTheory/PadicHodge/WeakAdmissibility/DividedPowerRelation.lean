import OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients

/-! # Divided Power Relation -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRelation

noncomputable section

/-! The completed divided-power relation xi-X and its coefficient recurrence. -/

open AdicCompletion OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients.Series
variable {R : Type*} [CommRing R]

def dividedPowerShift : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.linearCombination R (fun n : ℕ => Finsupp.single (n + 1) (n + 1 : R))

theorem dividedPowerShift_zero (f : ℕ →₀ R) : dividedPowerShift f 0 = 0 := by
  simp [dividedPowerShift, Finsupp.linearCombination_apply, Finsupp.sum]

theorem dividedPowerShift_succ (f : ℕ →₀ R) (n : ℕ) :
    dividedPowerShift f (n + 1) = (n + 1 : ℕ) * f n := by
  classical
  change (f.sum fun i c => c • Finsupp.single (i + 1) (i + 1 : R)) (n + 1) = _
  rw [Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single n]
  · simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one]
  · intro i _ hin
    simp only [Finsupp.smul_apply, Finsupp.single_apply, Nat.add_left_inj, hin, ↓reduceIte, smul_zero]
  · intro _
    simp only [zero_smul, Finsupp.zero_apply]

def dividedPowerRelation (ξ : R) : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R) :=
  ξ • LinearMap.id - dividedPowerShift

theorem dividedPowerRelation_zero (ξ : R) (f : ℕ →₀ R) : dividedPowerRelation ξ f 0 = ξ * f 0 := by
  change ξ * f 0 - dividedPowerShift f 0 = _
  rw [dividedPowerShift_zero, sub_zero]

theorem dividedPowerRelation_succ (ξ : R) (f : ℕ →₀ R) (n : ℕ) :
    dividedPowerRelation ξ f (n + 1) = ξ * f (n + 1) - (n + 1 : ℕ) * f n := by
  change ξ * f (n + 1) - dividedPowerShift f (n + 1) = _
  rw [dividedPowerShift_succ]

theorem completed_relation_of_recurrence (q ξ : R)
    (c : AdicCauchySequence (Ideal.span {q}) (ℕ →₀ R)) (a b : ℕ → R)
    (hc : ∀ r i, q ^ r ∣ a i - c r i) (hb : RestrictedCoefficients.IsRestricted q b)
    (hzero : ξ * b 0 = a 0)
    (hrec : ∀ n : ℕ, ξ * b (n + 1) = a (n + 1) + (n + 1 : ℕ) * b n) :
    AdicCompletion.map (Ideal.span {q}) (dividedPowerRelation ξ) (RestrictedCoefficients.Series.restrictedSeries q b hb) =
      AdicCompletion.mk (Ideal.span {q}) (ℕ →₀ R) c := by
  rw [RestrictedCoefficients.Series.restrictedSeries, AdicCompletion.map_mk]
  apply RestrictedCoefficients.Series.completion_eq_of_coefficients q _ c a _ hc
  intro r i
  change q ^ r ∣ a i - dividedPowerRelation ξ (RestrictedCoefficients.Series.truncatedCauchy q b hb r) i
  cases i with
  | zero =>
    rw [dividedPowerRelation_zero, ← hzero, ← mul_sub]
    exact dvd_mul_of_dvd_right (RestrictedCoefficients.Series.truncatedCauchy_approx q b hb r 0) ξ
  | succ n =>
    rw [dividedPowerRelation_succ]
    have he : a (n + 1) = ξ * b (n + 1) - (n + 1 : ℕ) * b n := by
      linear_combination -(hrec n)
    rw [he]
    have hd := dvd_sub
      (dvd_mul_of_dvd_right (RestrictedCoefficients.Series.truncatedCauchy_approx q b hb r (n + 1)) ξ)
      (dvd_mul_of_dvd_right (RestrictedCoefficients.Series.truncatedCauchy_approx q b hb r n) (n + 1 : ℕ))
    convert hd using 1
    ring

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRelation
