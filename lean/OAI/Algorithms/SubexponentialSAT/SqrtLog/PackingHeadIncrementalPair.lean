import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramCounts

namespace OAI.Algorithms

/-! Exact uniform-completion values of one head-collision term. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open scoped BigOperators

variable {r Q : ℕ}

def collision (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) : ℚ :=
  if ω a t = ω b t then 1 else 0

def pairCount (alphabet : List (Word r Q)) (remaining : List ℕ)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) : ℕ :=
  scaledCount alphabet (fun η => if η a t = η b t then 1 else 0)
    {a, b} 4 remaining ω

theorem collision_dependsOn (t : Fin Q) (a b : ℕ) :
    DependsOn {a, b} (collision (r := r) t a b) := by
  intro ω η h
  simp only [collision, h a (by simp), h b (by simp)]

theorem collision_expectation (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) :
    wordExpectation alphabet (collision t a b) remaining ω =
      if a = b then 1 else
        if a ∈ remaining ∨ b ∈ remaining then 1 / (r : ℚ) else collision t a b ω := by
  by_cases hab : a = b
  · subst b
    have hfun : collision (r := r) t a a = fun _ => 1 := by
      funext η
      simp [collision]
    rw [hfun]
    simp only [ite_true]
    exact wordExpectation_const alphabet ha 1 remaining ω
  · simp only [ite_eq_right hab]
    induction remaining generalizing ω with
    | nil => simp [wordExpectation]
    | cons j remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      by_cases hr : a ∈ remaining ∨ b ∈ remaining
      · have hc : a ∈ j :: remaining ∨ b ∈ j :: remaining := by
          rcases hr with har | hbr
          · exact Or.inl (List.mem_cons_of_mem _ har)
          · exact Or.inr (List.mem_cons_of_mem _ hbr)
        simp only [ite_eq_left hr, ite_eq_left hc]
        exact SubexponentialSAT.LocalExpectation.mean_const alphabet ha _
      · obtain ⟨har, hbr⟩ := not_or.mp hr
        simp only [ite_eq_right hr]
        by_cases hja : j = a
        · subst j
          simp only [List.mem_cons, true_or, ite_true]
          simpa [collision, Function.update_of_ne (Ne.symm hab)] using hbalance t (ω b t)
        · by_cases hjb : j = b
          · subst j
            simp only [List.mem_cons, true_or, or_true, ite_true]
            simpa [collision, Function.update_of_ne hab, eq_comm] using hbalance t (ω a t)
          · have hc : ¬(a ∈ j :: remaining ∨ b ∈ j :: remaining) := by
              simp only [List.mem_cons]
              tauto
            simp only [ite_eq_right hc]
            have heq : (fun w => collision t a b (Function.update ω j w)) =
                fun _ => collision t a b ω := by
              funext w
              simp [collision, Function.update_of_ne (Ne.symm hja),
                Function.update_of_ne (Ne.symm hjb)]
            rw [heq]
            exact SubexponentialSAT.LocalExpectation.mean_const alphabet ha _

theorem pairCount_cast (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (hbalance : ∀ (t : Fin Q) (c : Fin r),
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => if w t = c then (1 : ℚ) else 0) = 1 / (r : ℚ))
    (remaining : List ℕ) (hn : remaining.Nodup)
    (t : Fin Q) (a b : ℕ) (ω : ℕ → Word r Q) :
    (pairCount alphabet remaining t a b ω : ℚ) =
      (alphabet.length : ℚ)^4 *
        (if a = b then 1 else if a ∈ remaining ∨ b ∈ remaining then 1 / (r : ℚ)
          else collision t a b ω) := by
  have hS : (active ({a,b} : Finset ℕ) remaining).length ≤ 4 := by
    have h := active_length_le ({a,b} : Finset ℕ) remaining hn
    have hc : ({a,b} : Finset ℕ).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hf := wordExpectation_filter alphabet ha ({a,b} : Finset ℕ)
    (collision (r := r) t a b) (collision_dependsOn t a b) remaining ω
  have hs := local_average_eq_scaledCount alphabet ha
    (fun η : ℕ → Word r Q => if η a t = η b t then 1 else 0)
    ({a,b} : Finset ℕ) 4 remaining hS ω
  have hdiv : wordExpectation alphabet (collision t a b) remaining ω =
      (pairCount alphabet remaining t a b ω : ℚ) / (alphabet.length : ℚ)^4 := by
    rw [hf]
    change wordExpectation alphabet (fun η => if η a t = η b t then 1 else 0)
      (active {a, b} remaining) ω = _
    simpa only [pairCount, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hs
  rw [collision_expectation alphabet ha hbalance] at hdiv
  have hq : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr ha).ne'
  have hmul := (eq_div_iff (pow_ne_zero 4 hq)).mp hdiv
  simpa only [mul_comm] using hmul.symm

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
