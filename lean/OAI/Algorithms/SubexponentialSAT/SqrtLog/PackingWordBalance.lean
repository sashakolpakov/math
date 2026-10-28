import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWords

namespace OAI.Algorithms

/-! Natural color counts in an explicit uniform word alphabet. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes

variable {r Q : ℕ} [NeZero r]

def wordColorCount (alphabet : List (Word r Q)) (t : Fin Q) (c : Fin r) : ℕ :=
  (alphabet.map (fun w => if w t = c then 1 else 0)).sum

omit [NeZero r] in
private theorem cast_indicator_sum (alphabet : List (Word r Q)) (t : Fin Q) (c : Fin r) :
    (wordColorCount alphabet t c : ℚ) =
      (alphabet.map (fun w => if w t = c then (1 : ℚ) else 0)).sum := by
  induction alphabet with
  | nil => simp [wordColorCount]
  | cons a as ih =>
    simp only [wordColorCount, List.map_cons, List.sum_cons, Nat.cast_add] at *
    rw [ih]
    split_ifs <;> simp

theorem mean_word_color (alphabet : List (Word r Q)) (hn : alphabet.Nodup)
    (hf : ∀ w, w ∈ alphabet) (t : Fin Q) (c : Fin r) :
    SubexponentialSAT.ConditionalExpectation.mean alphabet
      (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ) := by
  rw [SubexponentialSAT.TypeDistribution.list_mean_eq_uniform alphabet hn hf]
  simpa only [Fintype.card_fin] using
    (mean_eval t (fun a : Fin r => if a = c then (1 : ℚ) else 0)).trans
      (SubexponentialSAT.TypeDistribution.mean_indicator c)

theorem wordColorCount_div_length (alphabet : List (Word r Q)) (hn : alphabet.Nodup)
    (hf : ∀ w, w ∈ alphabet) (t : Fin Q) (c : Fin r) :
    (wordColorCount alphabet t c : ℚ) / (alphabet.length : ℚ) = 1 / (r : ℚ) := by
  rw [cast_indicator_sum]
  exact mean_word_color alphabet hn hf t c

theorem wordColorCount_mul (alphabet : List (Word r Q)) (hn : alphabet.Nodup)
    (hf : ∀ w, w ∈ alphabet) (t : Fin Q) (c : Fin r) :
    wordColorCount alphabet t c * r = alphabet.length := by
  have ha : alphabet ≠ [] := by
    intro he
    have hc := hf (fun _ => c)
    simp [he] at hc
  have hq : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr ha).ne'
  have hr : (r : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have h := (div_eq_div_iff hq hr).mp (wordColorCount_div_length alphabet hn hf t c)
  have he : (wordColorCount alphabet t c : ℚ) * (r : ℚ) = (alphabet.length : ℚ) := by
    simpa using h
  exact_mod_cast he

theorem wordColorCount_eq (alphabet : List (Word r Q)) (hn : alphabet.Nodup)
    (hf : ∀ w, w ∈ alphabet) (t : Fin Q) (c d : Fin r) :
    wordColorCount alphabet t c = wordColorCount alphabet t d := by
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne r))
    ((wordColorCount_mul alphabet hn hf t c).trans (wordColorCount_mul alphabet hn hf t d).symm)

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
