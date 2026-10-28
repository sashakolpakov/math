import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Explicit polynomial envelopes for a fixed number of layout stages. -/

namespace SubexponentialSAT.SubexpMainLayoutPolynomial

def step (C d X W : ℕ) : ℕ := W + C * (W + X + 1) ^ d + 1

def grow (C d X : ℕ) : ℕ → ℕ
  | 0 => X
  | n + 1 => step C d X (grow C d X n)

def coefficient (C d : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => coefficient C d n + C * (coefficient C d n + 1) ^ d + 1

def degree (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (degree d n + 1) * (d + 1)

theorem step_mono {C C' d d' X X' W W' : ℕ}
    (hC : C ≤ C') (hd : d ≤ d') (hX : X ≤ X') (hW : W ≤ W') :
    step C d X W ≤ step C' d' X' W' := by
  have hbase : W + X + 1 ≤ W' + X' + 1 := by omega
  have hpow := (Nat.pow_le_pow_left hbase d).trans
    (Nat.pow_le_pow_right (by omega : 0 < W' + X' + 1) hd)
  exact Nat.add_le_add_right (Nat.add_le_add hW (Nat.mul_le_mul hC hpow)) 1

theorem step_monotone (C d X : ℕ) : Monotone (step C d X) :=
  fun _ _ h => step_mono le_rfl le_rfl le_rfl h

theorem le_step (C d X W : ℕ) : W ≤ step C d X W := by
  unfold step
  omega

theorem lt_step (C d X W : ℕ) : W < step C d X W := by
  unfold step
  omega

theorem grow_mono {C C' d d' X X' : ℕ}
    (hC : C ≤ C') (hd : d ≤ d') (hX : X ≤ X') (n : ℕ) :
    grow C d X n ≤ grow C' d' X' n := by
  induction n with
  | zero => exact hX
  | succ n ih => exact step_mono hC hd hX ih

theorem grow_monotone (C d n : ℕ) : Monotone (fun X => grow C d X n) :=
  fun _ _ h => grow_mono le_rfl le_rfl h n

theorem grow_le_succ (C d X n : ℕ) : grow C d X n ≤ grow C d X (n + 1) :=
  le_step C d X (grow C d X n)

theorem grow_mono_stage (C d X : ℕ) : Monotone (grow C d X) :=
  monotone_nat_of_le_succ (grow_le_succ C d X)

theorem grow_mono_all {C C' d d' X X' n n' : ℕ}
    (hC : C ≤ C') (hd : d ≤ d') (hX : X ≤ X') (hn : n ≤ n') :
    grow C d X n ≤ grow C' d' X' n' :=
  (grow_mono hC hd hX n).trans (grow_mono_stage C' d' X' hn)

theorem self_le_grow (C d X n : ℕ) : X ≤ grow C d X n :=
  grow_mono_stage C d X (Nat.zero_le n)

theorem coefficient_pos (C d n : ℕ) : 0 < coefficient C d n := by
  cases n <;> simp only [coefficient] <;> omega

theorem degree_pos (d n : ℕ) : 0 < degree d n := by
  cases n with
  | zero => exact Nat.zero_lt_one
  | succ n => exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

/-- Adding the original input costs at most one more factor of X+1. -/
theorem add_input_le {W A X e : ℕ} (hW : W ≤ A * (X + 1) ^ e) :
    W + X + 1 ≤ (A + 1) * (X + 1) ^ (e + 1) := by
  have hpow : (X + 1) ^ e ≤ (X + 1) ^ (e + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos X) (Nat.le_succ e)
  have hbase : X + 1 ≤ (X + 1) ^ (e + 1) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (Nat.succ_pos X) (Nat.succ_le_succ (Nat.zero_le e)) :
        (X + 1) ^ 1 ≤ (X + 1) ^ (e + 1))
  calc
    W + X + 1 = W + (X + 1) := by omega
    _ ≤ A * (X + 1) ^ (e + 1) + (X + 1) ^ (e + 1) :=
      Nat.add_le_add (hW.trans (Nat.mul_le_mul_left A hpow)) hbase
    _ = (A + 1) * (X + 1) ^ (e + 1) := by ring

theorem step_le_polynomial {W A X e C d : ℕ} (hW : W ≤ A * (X + 1) ^ e) :
    step C d X W ≤ (A + C * (A + 1) ^ d + 1) *
      (X + 1) ^ ((e + 1) * (d + 1)) := by
  have he : e ≤ (e + 1) * (d + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hed : (e + 1) * d ≤ (e + 1) * (d + 1) :=
    Nat.mul_le_mul_left (e + 1) (Nat.le_succ d)
  have hfirst : W ≤ A * (X + 1) ^ ((e + 1) * (d + 1)) :=
    hW.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (Nat.succ_pos X) he))
  have hmiddle : C * (W + X + 1) ^ d ≤
      C * (A + 1) ^ d * (X + 1) ^ ((e + 1) * (d + 1)) := by
    calc
      _ ≤ C * ((A + 1) * (X + 1) ^ (e + 1)) ^ d :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (add_input_le hW) d)
      _ = C * (A + 1) ^ d * (X + 1) ^ ((e + 1) * d) := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ _ := Nat.mul_le_mul_left (C * (A + 1) ^ d)
        (Nat.pow_le_pow_right (Nat.succ_pos X) hed)
  have hone : 1 ≤ (X + 1) ^ ((e + 1) * (d + 1)) :=
    Nat.one_le_pow _ _ (Nat.succ_pos X)
  calc
    step C d X W = W + C * (W + X + 1) ^ d + 1 := rfl
    _ ≤ A * (X + 1) ^ ((e + 1) * (d + 1)) +
        C * (A + 1) ^ d * (X + 1) ^ ((e + 1) * (d + 1)) +
        (X + 1) ^ ((e + 1) * (d + 1)) :=
      Nat.add_le_add (Nat.add_le_add hfirst hmiddle) hone
    _ = _ := by ring

theorem grow_le_polynomial (C d X n : ℕ) :
    grow C d X n ≤ coefficient C d n * (X + 1) ^ degree d n := by
  induction n with
  | zero => simp [grow, coefficient, degree]
  | succ n ih => exact step_le_polynomial ih

theorem grow_six_le_polynomial (C d X : ℕ) :
    grow C d X 6 ≤ coefficient C d 6 * (X + 1) ^ degree d 6 :=
  grow_le_polynomial C d X 6

end SubexponentialSAT.SubexpMainLayoutPolynomial

end OAI.Algorithms
