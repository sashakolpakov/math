import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Exact correspondence between the physical gated prefix and prior heads. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

def headRows {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) : List (List Bool) :=
  if fixed.length < heads then fixed.reverse.map ReadPlan.encodeWord else []

def overlap {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) : ℕ :=
  PackingHeadProgramPrefix.score (ReadPlan.encodeWord candidate) (headRows heads fixed)

def headCount {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) : ℕ :=
  if fixed.length < heads then fixed.length else 0

theorem encodedWords_length {r Q : ℕ} (ws : List (Word r Q)) :
    (ws.map ReadPlan.encodeWord).flatten.length=ws.length*ReadPlan.wordWidth r Q := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [List.flatten_cons,ih,Nat.add_mul,Nat.add_comm]

theorem headRows_length {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    (headRows heads fixed).length=headCount heads fixed := by
  unfold headRows headCount
  split <;> simp

theorem headRows_width {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (row : List Bool) (h : row ∈ headRows heads fixed) : row.length=ReadPlan.wordWidth r Q := by
  unfold headRows at h
  split at h
  · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact ReadPlan.encodeWord_length w
  · simp at h

theorem headCount_le {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    headCount heads fixed ≤ fixed.length := by
  unfold headCount
  split <;> omega

theorem take_headRows {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (suffix : List Bool) :
    ((fixed.reverse.map ReadPlan.encodeWord).flatten ++ suffix).take
      (headCount heads fixed*ReadPlan.wordWidth r Q) = (headRows heads fixed).flatten := by
  unfold headCount headRows
  split
  · exact List.take_left' (by simpa using encodedWords_length fixed.reverse)
  · simp

theorem take_headRows_memory {r Q : ℕ} (heads : ℕ) (a : Word r Q)
    (tail fixed : List (Word r Q)) (remaining : ℕ) (stk : Fin 48 → List Bool)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail remaining fixed stk) :
    (stk 8).take (headCount heads fixed*ReadPlan.wordWidth r Q) = (headRows heads fixed).flatten := by
  rw [hm.assignment,List.flatten_append]
  exact take_headRows heads fixed _

theorem headRows_fits_memory {r Q : ℕ} (heads : ℕ) (a : Word r Q)
    (tail fixed : List (Word r Q)) (remaining : ℕ) (stk : Fin 48 → List Bool)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail remaining fixed stk) :
    headCount heads fixed*ReadPlan.wordWidth r Q ≤ (stk 8).length := by
  rw [hm.assignment,List.flatten_append,List.length_append,encodedWords_length]
  have h := Nat.mul_le_mul_right (ReadPlan.wordWidth r Q) (headCount_le heads fixed)
  simpa only [List.length_reverse] using h.trans (Nat.le_add_right _ _)

theorem overlap_cases {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (candidate : Word r Q) : overlap heads fixed candidate =
      if fixed.length < heads then PackingHeadProgramPrefix.score (ReadPlan.encodeWord candidate)
        (fixed.reverse.map ReadPlan.encodeWord) else 0 := by
  unfold overlap headRows
  split <;> simp [PackingHeadProgramPrefix.score]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
