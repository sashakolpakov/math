import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingAlgorithm
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! Equality tests for shared-head incidence words and individual head colors. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
/-- Incidence equality reads the actual shared variable and shared factor seeds. -/
theorem incidenceType_eq_iff (ω η : WordAssignment V E r Q) (i j : I) :
    incidenceType ivar factor ω i = incidenceType ivar factor η j ↔
      ω (.inl (ivar i)) = η (.inl (ivar j)) ∧
      ω (.inr (factor i)) = η (.inr (factor j)) := by
  constructor
  · intro h
    exact ⟨congrArg UniversalType.head h,
      congrArg (fun u : UniversalType r Q 1 => u.slot 0) h⟩
  · rintro ⟨hh, hs⟩
    apply UniversalType.ext
    · exact hh
    · funext a
      exact hs

/-- Two word records are sufficient even when multiple incidences share a seed. -/
def incidenceWords (ω : WordAssignment V E r Q) (i : I) : List (Word r Q) :=
  [ω (.inl (ivar i)), ω (.inr (factor i))]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem incidenceWords_eq_iff (ω η : WordAssignment V E r Q) (i j : I) :
    incidenceWords ivar factor ω i = incidenceWords ivar factor η j ↔
      incidenceType ivar factor ω i = incidenceType ivar factor η j := by
  rw [incidenceType_eq_iff]
  simp [incidenceWords]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem decide_incidenceWords_eq (ω η : WordAssignment V E r Q) (i j : I) :
    decide (incidenceWords ivar factor ω i = incidenceWords ivar factor η j) =
      decide (incidenceType ivar factor ω i = incidenceType ivar factor η j) := by
  simp only [incidenceWords_eq_iff]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem decide_incidenceType_eq (ω η : WordAssignment V E r Q) (i j : I) :
    decide (incidenceType ivar factor ω i = incidenceType ivar factor η j) =
      (decide (ω (.inl (ivar i)) = η (.inl (ivar j))) &&
       decide (ω (.inr (factor i)) = η (.inr (factor j)))) := by
  simp [incidenceType_eq_iff]
end Incidences

/-- The finite Boolean cell used for one coordinate of a word. -/
def headColorBits {r Q : ℕ} (w : Word r Q) (t : Fin Q) : List Bool :=
  List.ofFn (fun c : Fin r => decide (w t = c))

@[simp] theorem headColorBits_length {r Q : ℕ} (w : Word r Q) (t : Fin Q) :
    (headColorBits w t).length = r := by simp [headColorBits]

theorem headColorBits_eq_iff {r Q : ℕ} (u v : Word r Q) (t : Fin Q) :
    headColorBits u t = headColorBits v t ↔ u t = v t := by
  constructor
  · intro h
    have hp := List.ofFn_inj.mp h
    have hc := congrFun hp (u t)
    have hvu : v t = u t := by simpa using hc
    exact hvu.symm
  · intro h
    simp [headColorBits, h]

theorem decide_headColorBits_eq {r Q : ℕ} (u v : Word r Q) (t : Fin Q) :
    decide (headColorBits u t = headColorBits v t) = decide (u t = v t) := by
  simp only [headColorBits_eq_iff]

theorem encodeWord_eq_headColorBits {r Q : ℕ} (w : Word r Q) :
    SubexponentialSAT.Subexp.ReadPlan.encodeWord w = (List.ofFn (headColorBits w)).flatten := rfl

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
