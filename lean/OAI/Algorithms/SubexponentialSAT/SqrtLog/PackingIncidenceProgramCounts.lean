import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramRefinement

namespace OAI.Algorithms

/-! Zero terms and append decomposition for the two concrete score producers. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

section General
variable {A W J : Type*} [DecidableEq A]

theorem completionCount_zero (alphabet : List W) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun _ => 0) remaining ω = 0 := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i rest ih => simp [completionCount, ih]

theorem scaledCount_zero (alphabet : List W) (support : Finset A) (S : ℕ)
    (remaining : List A) (ω : A → W) :
    scaledCount alphabet (fun _ => 0) support S remaining ω = 0 := by
  simp [scaledCount, completionCount_zero]

theorem commonNumerator_append (alphabet : List W) (left right : List J)
    (f : J → (A → W) → ℕ) (support : J → Finset A) (S : ℕ)
    (remaining : List A) (ω : A → W) :
    commonNumerator alphabet (left ++ right) f support S remaining ω =
      commonNumerator alphabet left f support S remaining ω +
      commonNumerator alphabet right f support S remaining ω := by
  simp [commonNumerator]
end General

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCount_headTerms_zero (alphabet : List (Word r Q))
    (heads : List (Fin Q × V × V)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet (heads.map Sum.inr) indices remaining ω).1 = 0 := by
  simp [unweightedCounts, commonNumerator, List.map_map, Function.comp_def,
    incidenceIndicator, scaledCount_zero]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem headCount_incidenceTerms_zero (alphabet : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices remaining ω).2 = 0 := by
  simp [unweightedCounts, commonNumerator, List.map_map, Function.comp_def,
    headIndicator, scaledCount_zero]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem unweightedCounts_append (alphabet : List (Word r Q))
    (left right : List (ScoreTerm I V Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    unweightedCounts ivar factor alphabet (left ++ right) indices remaining ω =
      ((unweightedCounts ivar factor alphabet left indices remaining ω).1 +
        (unweightedCounts ivar factor alphabet right indices remaining ω).1,
       (unweightedCounts ivar factor alphabet left indices remaining ω).2 +
        (unweightedCounts ivar factor alphabet right indices remaining ω).2) := by
  simp [unweightedCounts, commonNumerator_append]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem unweightedCounts_split (alphabet : List (Word r Q))
    (pairs : List (I × I)) (heads : List (Fin Q × V × V))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    unweightedCounts ivar factor alphabet (pairs.map Sum.inl ++ heads.map Sum.inr)
      indices remaining ω =
      ((unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices remaining ω).1,
       (unweightedCounts ivar factor alphabet (heads.map Sum.inr) indices remaining ω).2) := by
  rw [unweightedCounts_append, incidenceCount_headTerms_zero, headCount_incidenceTerms_zero]
  simp

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem weightedNumerator_split (alphabet : List (Word r Q))
    (pairs : List (I × I)) (heads : List (Fin Q × V × V))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    numerator ivar factor alphabet (pairs.map Sum.inl ++ heads.map Sum.inr)
      indices w remaining ω =
      w.incidence *
        (unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices remaining ω).1 +
      w.head *
        (unweightedCounts ivar factor alphabet (heads.map Sum.inr) indices remaining ω).2 := by
  rw [numerator_split, unweightedCounts_split]
end Scores
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
