import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramUniformBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopReplay

namespace OAI.Algorithms

/-! Storage bounds for the actual moment-loop tape transformations.  These
bounds use parsed payloads and dictionary invariants, never elapsed time. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls MomentsAssembly MomentsProgram

def WordCap (A : ℕ) (high : Fin 768 → List Bool) : Prop :=
  ∀ i, (high i).length ≤ A

theorem WordCap.mono {A C : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (hac : A ≤ C) : WordCap C high :=
  fun i => (h i).trans hac

theorem WordCap.update {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (i : Fin 768) (bits : List Bool) (hb : bits.length ≤ A) :
    WordCap A (Function.update high i bits) := by
  intro j
  by_cases he : j=i
  · subst j; simpa using hb
  · simpa [Function.update_of_ne he] using h j

theorem WordCap.masked {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) : WordCap A (LeafProgram.FactorLoop.maskedHigh high) := by
  intro i
  simp only [LeafProgram.FactorLoop.maskedHigh,ProgramTapeReplay.rebaseStacks]
  split_ifs
  · exact Nat.zero_le _
  · exact h i

theorem bucketStream_bound {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (seed source : List Bool)
    (hs : seed.length ≤ A) (ht : source.length ≤ A) :
    WordCap A (bucketStream high seed source) :=
  (h.update _ _ ht).update _ _ hs

theorem supportStream_bound {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (seed source : List Bool)
    (hs : seed.length ≤ A) (ht : source.length ≤ A) :
    WordCap A (supportStream high seed source) :=
  (h.update _ _ ht).update _ _ hs

theorem assignmentHigh_bound {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (x tail : List Bool)
    (hx : x.length ≤ A) (ht : tail.length ≤ A) :
    WordCap A (assignmentHigh high x tail) :=
  (h.update _ _ ht).update _ _ hx

theorem supportHigh_bound {A : ℕ} {high : Fin 768 → List Bool}
    (h : WordCap A high) (mask tail : List Bool)
    (hm : mask.length ≤ A) (ht : tail.length ≤ A) :
    WordCap A (supportHigh high mask tail) :=
  ((h.update _ _ ht).update _ _ hm).update _ _ (h 170)

theorem headHigh_bound {A : ℕ} {high : Fin 768 → List Bool}
    (hc : WordCap A high) (h : HeadInput) (tail : List Bool)
    (hm : h.mask.length ≤ A) (hx : h.context.length ≤ A)
    (ha : (rawFrames h.assignments).length ≤ A) (ht : tail.length ≤ A) :
    WordCap A (headHigh high h tail) := by
  intro i
  simp only [headHigh,headHigh3,headHigh2,headHigh1,Function.update_apply]
  split_ifs <;> first | assumption | exact Nat.zero_le _ | exact hc i

theorem bucketHigh_bound {A : ℕ} {high : Fin 768 → List Bool}
    (hc : WordCap A high) (b : BucketInput) (tail : List Bool)
    (hb : b.context.length ≤ A)
    (hh : (rawFrames (b.heads.map HeadInput.bits)).length ≤ A)
    (ht : tail.length ≤ A) : WordCap A (bucketHigh high b tail) := by
  intro i
  simp only [bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1,Function.update_apply]
  split_ifs <;> first | assumption | exact Nat.zero_le _ | exact hc 169 | exact hc i

/-- Each dictionary is bounded by its genuine support/key invariant. -/
theorem dictionary_bound {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d))
    (h : EntryInvariant vars u J entries) :
    (Product.bytes entries).length ≤
      dictionaryByteEnvelope B d (n+u+J) (dictionaryCapacity vars u J) :=
  (entryInvariant_sizes vars u J entries h).2

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
