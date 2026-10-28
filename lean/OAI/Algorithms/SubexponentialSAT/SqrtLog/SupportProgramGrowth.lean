import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramCount
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleData

namespace OAI.Algorithms

/-! Each growth stage expands only the currently retained masks, then prunes.
The intermediate candidate list contains at most twice the final support count. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram

/-- Prepending presentation of one breadth-first growth stage. -/
def grow (J : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (rows.flatMap fun xs => [false :: xs, true :: xs]).filter (fun xs => decide (xs.count true < J))

theorem mem_grow (J : ℕ) (rows : List (List Bool)) (xs : List Bool) :
    xs ∈ grow J rows ↔ ∃ b ys, ys ∈ rows ∧ xs = b :: ys ∧ xs.count true < J := by
  cases xs with
  | nil => simp [grow]
  | cons b xs => cases b <;> simp [grow, and_assoc]

theorem grow_nodup (J : ℕ) (rows : List (List Bool)) (h : rows.Nodup) :
    (grow J rows).Nodup := by
  apply List.Nodup.filter
  induction rows with
  | nil => simp
  | cons xs rows ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append]
      obtain ⟨hx, hr⟩ := List.nodup_cons.mp h
      have hi := ih hr
      simp only [List.nodup_cons]
      refine ⟨?_, ?_, hi⟩
      · simp only [List.mem_cons, List.mem_flatMap, not_or]
        constructor
        · simp
        · rintro ⟨ys, hy, he⟩
          have heq : xs = ys := by simpa using he
          exact hx (heq.symm ▸ hy)
      · simp only [List.mem_flatMap]
        rintro ⟨ys, hy, he⟩
        have heq : xs = ys := by simpa using he
        exact hx (heq.symm ▸ hy)

def levels (J : ℕ) : ℕ → List (List Bool)
  | 0 => if J = 0 then [] else [[]]
  | n + 1 => grow J (levels J n)

@[simp] theorem mem_levels (J n : ℕ) (xs : List Bool) :
    xs ∈ levels J n ↔ xs.length = n ∧ xs.count true < J := by
  induction n generalizing xs with
  | zero => cases xs <;> cases J <;> simp [levels]
  | succ n ih =>
      rw [levels, mem_grow]
      constructor
      · rintro ⟨b, ys, hys, rfl, hw⟩
        exact ⟨by simp [(ih ys).mp hys |>.1], hw⟩
      · rintro ⟨hlen, hw⟩
        cases xs with
        | nil => simp at hlen
        | cons b xs =>
            refine ⟨b, xs, (ih xs).mpr ⟨by simpa using hlen, ?_⟩, rfl, hw⟩
            cases b <;> simp at hw ⊢ <;> omega

theorem levels_nodup (J n : ℕ) : (levels J n).Nodup := by
  induction n with
  | zero => simp [levels]; split <;> simp
  | succ n ih => exact grow_nodup J _ ih

theorem levels_perm_masks (J n : ℕ) : (levels J n).Perm (masks n J) := by
  apply List.perm_ext_iff_of_nodup (levels_nodup J n) (masks_nodup n J) |>.mpr
  intro xs
  simp

@[simp] theorem levels_length (J n : ℕ) : (levels J n).length = count n J := by
  rw [(levels_perm_masks J n).length_eq, masks_length]

theorem count_mono_variables (J : ℕ) : Monotone (fun n => count n J) := by
  apply monotone_nat_of_le_succ
  intro n
  cases J with
  | zero => simp
  | succ J => rw [count_pascal]; omega

theorem growth_candidates_length (J i n : ℕ) (h : i ≤ n) :
    ((levels J i).flatMap fun xs => [false :: xs, true :: xs]).length ≤ 2 * count n J := by
  have he : ∀ rows : List (List Bool),
      (rows.flatMap fun xs => [false :: xs, true :: xs]).length = 2 * rows.length := by
    intro rows
    induction rows <;> simp_all ; omega
  rw [he, levels_length]
  exact Nat.mul_le_mul_left 2 (count_mono_variables J h)

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
