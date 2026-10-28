import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingAlgorithm
import OAI.Algorithms.SubexponentialSAT.Subexp.NaturalAssignment

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

structure Weights where
  incidence : ℕ
  head : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator

section General
variable {A W J : Type*} [DecidableEq A]

private theorem sum_map_div (xs : List J) (f : J → ℚ) (d : ℚ) :
    (xs.map (fun j => f j / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp [ih, add_div]

private theorem sum_map_le_bound (xs : List J) (f : J → ℕ) (B : ℕ)
    (hf : ∀ j, f j ≤ B) : (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      _ ≤ B + xs.length * B := Nat.add_le_add (hf j) ih
      _ = _ := by ring

theorem wordExpectation_div (alphabet : List W) (f : (A → W) → ℚ)
    (remaining : List A) (ω : A → W) (d : ℚ) :
    wordExpectation alphabet (fun η => f η / d) remaining ω =
      wordExpectation alphabet f remaining ω / d := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
    simp only [wordExpectation, SubexponentialSAT.ConditionalExpectation.mean]
    simp_rw [ih]
    rw [sum_map_div]
    ring

theorem completionCount_bound (alphabet : List W) (f : (A → W) → ℕ)
    (B : ℕ) (hf : ∀ ω, f ω ≤ B) (remaining : List A) (ω : A → W) :
    completionCount alphabet f remaining ω ≤ B * alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => simpa [completionCount] using hf ω
  | cons i remaining ih =>
    simp only [completionCount, List.length_cons]
    calc
      _ ≤ alphabet.length * (B * alphabet.length ^ remaining.length) :=
        sum_map_le_bound alphabet _ _ (fun w => ih _)
      _ = _ := by rw [pow_succ]; ring

theorem commonNumerator_bound (alphabet : List W) (terms : List J)
    (f : J → (A → W) → ℕ) (support : J → Finset A) (S B : ℕ)
    (remaining : List A) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (hf : ∀ j ω, f j ω ≤ B) (ω : A → W) :
    commonNumerator alphabet terms f support S remaining ω ≤
      terms.length * (B * alphabet.length ^ S) := by
  apply sum_map_le_bound
  intro j
  unfold scaledCount
  calc
    _ ≤ alphabet.length ^ (S - (active (support j) remaining).length) *
        (B * alphabet.length ^ (active (support j) remaining).length) :=
      Nat.mul_le_mul_left _ (completionCount_bound alphabet (f j) B (hf j) _ ω)
    _ = B * alphabet.length ^ S := by
      rw [← mul_assoc, mul_comm _ B, mul_assoc, ← pow_add, Nat.sub_add_cancel (hS j)]

theorem localEvaluator_div_numerator (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (f : J → (A → W) → ℕ) (support : J → Finset A) (S : ℕ)
    (remaining : List A) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (ω : A → W) (d offset : ℚ) :
    localEvaluator alphabet terms support (fun j η => (f j η : ℚ) / d)
      offset remaining ω =
      (commonNumerator alphabet terms f support S remaining ω : ℚ) /
        (d * (alphabet.length : ℚ)^S) - offset := by
  unfold localEvaluator
  simp_rw [wordExpectation_div,
    local_average_eq_scaledCount alphabet ha _ _ S remaining (hS _) ω]
  rw [sum_map_div, sum_map_div]
  have hc : (terms.map (fun j =>
      (scaledCount alphabet (f j) (support j) S remaining ω : ℚ))).sum =
      (commonNumerator alphabet terms f support S remaining ω : ℚ) := by
    simp [commonNumerator, Function.comp_def]
  rw [hc]
  ring
end General

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def naturalTerm (w : Weights) : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl (i,j), ω => if incidenceType ivar factor ω i = incidenceType ivar factor ω j
      then w.incidence else 0
  | .inr (t,v,u), ω => if ω (.inl v) t = ω (.inl u) t then w.head else 0

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem naturalTerm_le (w : Weights) (z : ScoreTerm I V Q)
    (ω : WordAssignment V E r Q) :
    naturalTerm ivar factor w z ω ≤ w.incidence + w.head := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp only [naturalTerm]; split_ifs <;> omega
  | inr p => rcases p with ⟨t,v,u⟩; simp only [naturalTerm]; split_ifs <;> omega

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem naturalTerm_div (w : Weights) (x y : ℚ)
    (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (z : ScoreTerm I V Q) (ω : WordAssignment V E r Q) :
    scoreTerm ivar factor x y z ω =
      (naturalTerm ivar factor w z ω : ℚ) / w.denominator := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp only [scoreTerm, naturalTerm]; split_ifs <;> simp [hy]
  | inr p => rcases p with ⟨t,v,u⟩; simp only [scoreTerm, naturalTerm]; split_ifs <;> simp [hx]

def numberedTerm (indices : List (V ⊕ E)) (w : Weights) (z : ScoreTerm I V Q)
    (ω : ℕ → Word r Q) : ℕ :=
  naturalTerm ivar factor w z (fun i => ω (indexCode indices i))

def numerator (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ)
    (ω : ℕ → Word r Q) : ℕ :=
  commonNumerator alphabet terms (numberedTerm ivar factor indices w)
    (numberedScoreSupport ivar factor indices) 4 remaining ω

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numerator_bound (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ)
    (hr : remaining.Nodup) (ω : ℕ → Word r Q) :
    numerator ivar factor alphabet terms indices w remaining ω ≤
      terms.length * ((w.incidence+w.head) * alphabet.length^4) := by
  apply commonNumerator_bound
  · intro z
    exact (active_length_le _ _ hr).trans
      (numberedScoreSupport_card_le ivar factor indices z)
  · intro z η
    exact naturalTerm_le ivar factor w z _

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluator_eq_numerator (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (remaining : List ℕ) (hr : remaining.Nodup) (ω : ℕ → Word r Q) (offset : ℚ) :
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining ω =
      (numerator ivar factor alphabet terms indices w remaining ω : ℚ) /
        ((w.denominator : ℚ) * (alphabet.length : ℚ)^4) - offset := by
  have hf : numberedScoreTerm (r := r) (Q := Q) ivar factor indices x y =
      fun z η => (numberedTerm ivar factor indices w z η : ℚ)/(w.denominator : ℚ) := by
    funext z η
    exact naturalTerm_div ivar factor w x y hy hx z _
  rw [hf]
  apply localEvaluator_div_numerator alphabet ha
  intro z
  exact (active_length_le _ _ hr).trans
    (numberedScoreSupport_card_le ivar factor indices z)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluator_le_iff (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (remaining : List ℕ) (hr : remaining.Nodup) (ω η : ℕ → Word r Q) (offset : ℚ) :
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining ω ≤
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining η ↔
    numerator ivar factor alphabet terms indices w remaining ω ≤
      numerator ivar factor alphabet terms indices w remaining η := by
  rw [evaluator_eq_numerator ivar factor alphabet ha terms indices w x y hy hx remaining hr ω offset,
    evaluator_eq_numerator ivar factor alphabet ha terms indices w x y hy hx remaining hr η offset,
    sub_le_sub_iff_right, div_le_div_iff_of_pos_right]
  · exact_mod_cast Iff.rfl
  · have hq : (0 : ℚ) < alphabet.length := by exact_mod_cast List.length_pos_iff.mpr ha
    have hw : (0 : ℚ) < w.denominator := by exact_mod_cast w.denominator_pos
    positivity
end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
