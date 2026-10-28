import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormSymmetry

/-! # Quaternion Norm Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormUniversality.PositiveQuaternionNorm

noncomputable section

/-! Every positive rational is represented by `1, 1, d, d` when `d` is
positive. The proof descends on the sum of two positive integers, using
norm symmetry, a bounded two-square congruence, and norm multiplication.
The final step clears rational denominators by squares. -/

private theorem small_prime_multiple (d p : ℕ) (hd : 0 < d)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ≤ p) :
    ∃ x y m : ℕ, 0 < m ∧ m < p ∧ x^2 + y^2 + d = m * p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := Nat.sq_add_sq_zmodEq p (-(d : ℤ))
  obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hxy.symm
  rw [sub_neg_eq_add, mul_comm] at hm
  have hm0 : 0 < m := by
    apply pos_of_mul_pos_left (b := (p : ℤ))
    · rw [← hm]
      have hd' : (0 : ℤ) < d := by exact_mod_cast hd
      positivity
    · exact Nat.cast_nonneg p
  lift m to ℕ using hm0.le
  have hmeq : x^2 + y^2 + d = m * p := by exact_mod_cast hm
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hx2 : 2 * x ≤ p := (Nat.mul_le_mul_left 2 hx).trans (Nat.mul_div_le p 2)
  have hy2 : 2 * y ≤ p := (Nat.mul_le_mul_left 2 hy).trans (Nat.mul_div_le p 2)
  have hxx := Nat.pow_le_pow_left hx2 2
  have hyy := Nat.pow_le_pow_left hy2 2
  refine ⟨x, y, m, by exact_mod_cast hm0, ?_, hmeq⟩
  by_contra hmp
  have hp_le_m : p ≤ m := Nat.le_of_not_gt hmp
  have hprod := Nat.mul_le_mul_right p hp_le_m
  have hp_square := Nat.mul_le_mul_right p hp3
  nlinarith

private theorem ordered_nat_represents (d a : ℕ) (hd : 0 < d) (ha : 0 < a)
    (hda : d ≤ a)
    (hsmall : ∀ d' a' : ℕ, d' + a' < d + a → 0 < d' → 0 < a' →
      QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d' : ℚ) (a' : ℚ)) : QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d : ℚ) (a : ℚ) := by
  by_cases ha1 : a = 1
  · subst a
    simpa using QuaternionNormSymmetry.PositiveQuaternionNorm.represents_one (d : ℚ)
  by_cases hp : a.Prime
  · by_cases ha2 : a = 2
    · subst a
      simpa using QuaternionNormSymmetry.PositiveQuaternionNorm.represents_two (d : ℚ)
    obtain ⟨x, y, m, hm0, hma, hmeq⟩ := small_prime_multiple d a hd hp ha2 hda
    have hm := hsmall d m (by omega) hd hm0
    have hmne : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
    have hmaRep : QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d : ℚ) ((m : ℚ) * a) := by
      refine ⟨(((x : ℚ), (y : ℚ)), (1, 0)), ?_⟩
      simp only [QuaternionNormSymmetry.PositiveQuaternionNorm.form_apply, one_pow, zero_pow (by decide : 2 ≠ 0), add_zero, mul_one]
      exact_mod_cast hmeq
    have hquot := hmaRep.div hm hmne
    simpa only [mul_div_cancel_left₀ _ hmne] using hquot
  · obtain ⟨u, v, hua, hva, huv⟩ :=
      (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ a)).mp hp
    have hpos : 0 < u * v := by rw [huv]; exact ha
    have hu0 : 0 < u := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hpos)
    have hu := hsmall d u (by omega) hd hu0
    have hv := hsmall d v (by omega) hd hv0
    simpa only [← Nat.cast_mul, huv] using hu.mul hv

private theorem nat_represents_aux (n : ℕ) :
    ∀ d a : ℕ, d + a = n → 0 < d → 0 < a → QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d : ℚ) (a : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d a hn hd ha
    have hs (d' a' : ℕ) (hlt : d' + a' < d + a) (hd' : 0 < d') (ha' : 0 < a') :
        QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d' : ℚ) (a' : ℚ) :=
      ih (d' + a') (by omega) d' a' rfl hd' ha'
    rcases le_total d a with hda | had
    · exact ordered_nat_represents d a hd ha hda hs
    · apply (QuaternionNormSymmetry.PositiveQuaternionNorm.represents_swap (by exact_mod_cast hd) (by exact_mod_cast ha)).mpr
      apply ordered_nat_represents a d ha hd had
      intro d' a' hlt hd' ha'
      exact hs d' a' (by omega) hd' ha'

theorem nat_represents (d a : ℕ) (hd : 0 < d) (ha : 0 < a) :
    QuaternionNormSymmetry.PositiveQuaternionNorm.Represents (d : ℚ) (a : ℚ) := nat_represents_aux (d + a) d a rfl hd ha

private theorem positive_integer_square_multiple (a : ℚ) (ha : 0 < a) :
    ∃ n : ℕ, ∃ c : ℚ, 0 < n ∧ 0 < c ∧ (n : ℚ) = a * c^2 := by
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have habs : (a.num.natAbs : ℚ) = a.num := by
    have h := congrArg (fun n : ℤ => (n : ℚ)) (Int.natAbs_of_nonneg hnum.le)
    simpa only [Int.cast_natCast] using h
  refine ⟨a.num.natAbs * a.den, a.den, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (Int.natAbs_pos.mpr (ne_of_gt hnum)) a.den_pos
  · exact_mod_cast a.den_pos
  · push_cast
    rw [habs]
    conv_rhs =>
      arg 1
      rw [← a.num_div_den]
    field_simp

theorem positive_rational_represents (d a : ℚ) (hd : 0 < d) (ha : 0 < a) :
    QuaternionNormSymmetry.PositiveQuaternionNorm.Represents d a := by
  obtain ⟨D, c, hD, hc, hDc⟩ := positive_integer_square_multiple d hd
  obtain ⟨A, e, hA, he, hAe⟩ := positive_integer_square_multiple a ha
  obtain ⟨u, hu⟩ := nat_represents D A hD hA
  let v : QuaternionNormSymmetry.PositiveQuaternionNorm.Vector := (u.1, (c * u.2.1, c * u.2.2))
  have hv : QuaternionNormSymmetry.PositiveQuaternionNorm.form d v = QuaternionNormSymmetry.PositiveQuaternionNorm.form (D : ℚ) u := by
    simp only [QuaternionNormSymmetry.PositiveQuaternionNorm.form_apply, v, hDc]
    ring
  refine ⟨e⁻¹ • v, ?_⟩
  rw [(QuaternionNormSymmetry.PositiveQuaternionNorm.form d).map_smul, smul_eq_mul, hv, hu, hAe]
  field_simp

theorem exists_weighted_four_squares (d a : ℚ) (hd : 0 < d) (ha : 0 < a) :
    ∃ x₁ x₂ y₁ y₂ : ℚ, x₁^2 + x₂^2 + d * (y₁^2 + y₂^2) = a := by
  obtain ⟨u, hu⟩ := positive_rational_represents d a hd ha
  exact ⟨u.1.1, u.1.2, u.2.1, u.2.2, (QuaternionNormSymmetry.PositiveQuaternionNorm.form_apply d u).symm.trans hu⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuaternionNormUniversality.PositiveQuaternionNorm
