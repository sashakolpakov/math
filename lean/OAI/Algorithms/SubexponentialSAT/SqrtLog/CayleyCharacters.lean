import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Real Walsh characters of the Boolean cube, with unnormalized Fourier sums. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

abbrev Cube (r : ℕ) := Fin r → ZMod 2

noncomputable def bitSign (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, bitSign, eq_self, ite_true, one_mul]
  by_cases hb : b = 0
  · subst b
    simp only [add_zero, bitSign, eq_self, ite_true, mul_one]
  have ha1 : a = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    have hlt := a.val_lt
    omega
  have hb1 : b = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
    have hlt := b.val_lt
    omega
  have hab : a + b = 0 := by
    rw [ha1, hb1]
    exact CharTwo.add_self_eq_zero 1
  unfold bitSign
  rw [ite_eq_left hab, ite_eq_right ha, ite_eq_right hb]
  norm_num

@[simp] theorem bitSign_sq (a : ZMod 2) : bitSign a ^ 2 = 1 := by
  simp only [bitSign]
  split_ifs <;> norm_num

theorem bitSign_eq_one_or_neg_one (a : ZMod 2) : bitSign a = 1 ∨ bitSign a = -1 := by
  simp only [bitSign]
  split_ifs <;> simp

noncomputable def character {r : ℕ} (a x : Cube r) : ℝ :=
  ∏ j, bitSign (a j * x j)

@[simp] theorem character_zero_left {r : ℕ} (x : Cube r) : character 0 x = 1 := by
  simp [character]

@[simp] theorem character_zero_right {r : ℕ} (a : Cube r) : character a 0 = 1 := by
  simp [character]

theorem character_comm {r : ℕ} (a x : Cube r) : character a x = character x a := by
  simp only [character, mul_comm]

theorem character_add_right {r : ℕ} (a x y : Cube r) :
    character a (x + y) = character a x * character a y := by
  simp only [character, Pi.add_apply, mul_add, bitSign_add, Finset.prod_mul_distrib]

theorem character_add_left {r : ℕ} (a b x : Cube r) :
    character (a + b) x = character a x * character b x := by
  rw [character_comm, character_add_right, character_comm x a, character_comm x b]

@[simp] theorem character_sq {r : ℕ} (a x : Cube r) : character a x ^ 2 = 1 := by
  rw [character, ← Finset.prod_pow]
  simp

theorem character_eq_one_or_neg_one {r : ℕ} (a x : Cube r) :
    character a x = 1 ∨ character a x = -1 := by
  have h := character_sq a x
  rcases sq_eq_one_iff.mp h with h | h
  · exact Or.inl h
  · exact Or.inr h

@[simp] theorem cube_add_self {r : ℕ} (x : Cube r) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

@[simp] theorem cube_card (r : ℕ) : Fintype.card (Cube r) = 2 ^ r := by
  simp [Cube]

theorem character_sum {r : ℕ} (a : Cube r) :
    (∑ x : Cube r, character a x) = if a = 0 then (Fintype.card (Cube r) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    unfold character
    rw [← Fintype.prod_sum (fun j (z : ZMod 2) => bitSign (a j * z))]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hlocal : ∀ b : ZMod 2, b ≠ 0 → (∑ z : ZMod 2, bitSign (b * z)) = 0 := by
      intro b hb
      have hb1 : b = 1 := by
        apply ZMod.val_injective
        rw [ZMod.val_one]
        have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
        have hlt := b.val_lt
        omega
      subst b
      have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
        decide
      rw [hu]
      rw [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
      rw [one_mul, one_mul, bitSign_zero, bitSign_one]
      norm_num
    exact hlocal (a j) hj

theorem character_sum_of_ne_zero {r : ℕ} (a : Cube r) (ha : a ≠ 0) :
    (∑ x : Cube r, character a x) = 0 := by rw [character_sum, ite_eq_right ha]

theorem character_orthogonal {r : ℕ} (x y : Cube r) :
    (∑ a : Cube r, character a x * character a y) =
      if x = y then (Fintype.card (Cube r) : ℝ) else 0 := by
  simp_rw [← character_add_right, character_comm _ (x + y)]
  rw [character_sum]
  have heq : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have := congrArg (fun z : Cube r => z + y) h
      simpa only [add_assoc, cube_add_self, add_zero, zero_add] using this
    · rintro rfl
      exact cube_add_self _
  simp only [heq]

noncomputable def fourier {r : ℕ} (f : Cube r → ℝ) (a : Cube r) : ℝ :=
  ∑ x, f x * character a x

@[simp] theorem fourier_zero {r : ℕ} (f : Cube r → ℝ) : fourier f 0 = ∑ x, f x := by
  simp [fourier]

noncomputable def walsh {r : ℕ} {P : Type*} [Fintype P]
    (shifts : P → Cube r) (a : Cube r) : ℝ := ∑ i, character a (shifts i)

def SmallWalsh {r : ℕ} {P : Type*} [Fintype P] (shifts : P → Cube r) (ε : ℝ) : Prop :=
  ∀ a, a ≠ 0 → |walsh shifts a| ≤ ε * Fintype.card P

@[simp] theorem walsh_zero {r : ℕ} {P : Type*} [Fintype P] (shifts : P → Cube r) :
    walsh shifts 0 = Fintype.card P := by simp [walsh]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
