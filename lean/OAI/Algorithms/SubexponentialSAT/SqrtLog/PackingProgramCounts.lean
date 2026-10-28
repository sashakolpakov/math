import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramScores

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

private theorem sum_linear {J : Type*} (xs : List J) (f g : J → ℕ) (a b : ℕ) :
    (xs.map (fun j => a*f j+b*g j)).sum = a*(xs.map f).sum+b*(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

section Linear
variable {A W J : Type*} [DecidableEq A]

theorem completionCount_linear (alphabet : List W) (f g : (A → W) → ℕ)
    (a b : ℕ) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun η => a*f η+b*g η) remaining ω =
      a*completionCount alphabet f remaining ω + b*completionCount alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
    simp only [completionCount]
    simp_rw [ih]
    exact sum_linear _ _ _ _ _

theorem commonNumerator_linear (alphabet : List W) (terms : List J)
    (f g : J → (A → W) → ℕ) (support : J → Finset A) (S a b : ℕ)
    (remaining : List A) (ω : A → W) :
    commonNumerator alphabet terms (fun j η => a*f j η+b*g j η) support S remaining ω =
      a*commonNumerator alphabet terms f support S remaining ω +
      b*commonNumerator alphabet terms g support S remaining ω := by
  unfold commonNumerator
  have hlocal (j : J) : scaledCount alphabet (fun η => a*f j η+b*g j η)
      (support j) S remaining ω = a*scaledCount alphabet (f j) (support j) S remaining ω +
        b*scaledCount alphabet (g j) (support j) S remaining ω := by
    unfold scaledCount
    rw [completionCount_linear]
    ring
  simp_rw [hlocal]
  exact sum_linear _ _ _ _ _
end Linear

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def incidenceIndicator : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl (i,j), ω => if incidenceType ivar factor ω i = incidenceType ivar factor ω j then 1 else 0
  | .inr _, _ => 0

def headIndicator : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl _, _ => 0
  | .inr (t,v,u), ω => if ω (.inl v) t = ω (.inl u) t then 1 else 0

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem naturalTerm_split (w : Weights) (z : ScoreTerm I V Q)
    (ω : WordAssignment V E r Q) :
    naturalTerm ivar factor w z ω =
      w.incidence * incidenceIndicator ivar factor z ω + w.head * headIndicator z ω := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp only [naturalTerm, incidenceIndicator, headIndicator]; split_ifs <;> simp
  | inr p => rcases p with ⟨t,v,u⟩; simp only [naturalTerm, incidenceIndicator, headIndicator]; split_ifs <;> simp

def unweightedCounts (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) : ℕ × ℕ :=
  (commonNumerator alphabet terms
    (fun z η => incidenceIndicator ivar factor z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 remaining ω,
   commonNumerator alphabet terms
    (fun z η => headIndicator z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 remaining ω)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numerator_split (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    numerator ivar factor alphabet terms indices w remaining ω =
      w.incidence * (unweightedCounts ivar factor alphabet terms indices remaining ω).1 +
      w.head * (unweightedCounts ivar factor alphabet terms indices remaining ω).2 := by
  unfold numerator numberedTerm
  simp_rw [naturalTerm_split]
  exact commonNumerator_linear _ _ _ _ _ _ _ _ _ _

def sequentialNumerator (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  numerator ivar factor alphabet terms indices w (List.range' fixed.length n) (decode default fixed)

omit [Fintype E] [DecidableEq I] in
theorem naturalAssignment_eq (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator) (n : ℕ) (fixed : List (Word r Q)) :
    SubexponentialSAT.Subexp.NaturalAssignment.assignNat a tail
      (sequentialNumerator ivar factor (a::tail) terms indices w a) n fixed =
    SubexponentialSAT.ConditionalExpectation.assignWithEvaluator a tail
      (sequentialEvaluator (a::tail) terms (numberedScoreSupport ivar factor indices)
        (numberedScoreTerm ivar factor indices x y)
        (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a) n fixed := by
  apply SubexponentialSAT.Subexp.NaturalAssignment.assignNat_eq_assignWithEvaluator
  intro n fixed u v
  exact evaluator_le_iff ivar factor (a::tail) (List.cons_ne_nil _ _) terms indices w
    x y hy hx (List.range' (u::fixed).length n) List.nodup_range'
    (decode a (u::fixed)) (decode a (v::fixed)) _
end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
