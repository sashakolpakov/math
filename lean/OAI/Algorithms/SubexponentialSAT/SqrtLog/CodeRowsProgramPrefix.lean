import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlots
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramVertex
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramEncoding

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def shiftRows {r : ℕ} (xs : List (Cayley.Cube r)) : List Bool :=
  xs.flatMap fun v => Shift.frames (vertexBits v)

theorem shiftRows_cons {r : ℕ} (v : Cayley.Cube r) (vs : List (Cayley.Cube r)) :
    shiftRows (v::vs)=Shift.frames (vertexBits v)++shiftRows vs := by
  simp [shiftRows]

theorem matrixFrames_shifts {r D : ℕ} (shifts : Fin D → Cayley.Cube r) :
    CodeSearchProgram.matrixFrames shifts=shiftRows (List.ofFn shifts) := by
  rw [matrixFrames_rows]
  simp only [shiftRows,List.flatMap,List.map_ofFn,Function.comp_def,vertexFrames]

theorem scalar_drop_head {D : ℕ} (q : Fin D → SparseCode.F3) (i : ℕ) (hi : i < D) :
    CodeSearchProgram.scalarFrames ((List.ofFn q).drop i)=
      Cell.frame (decide (q ⟨i,hi⟩=1)) (decide (q ⟨i,hi⟩=2)) ++
        CodeSearchProgram.scalarFrames ((List.ofFn q).drop (i+1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp [ternary_frames]

theorem shifts_drop_head {r D : ℕ} (shifts : Fin D → Cayley.Cube r) (i : ℕ) (hi : i < D) :
    shiftRows ((List.ofFn shifts).drop i)=Shift.frames (vertexBits (shifts ⟨i,hi⟩))++
      shiftRows ((List.ofFn shifts).drop (i+1)) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi),shiftRows_cons]
  simp

def prefixSlots {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i : ℕ) : List (Fin m × SparseCode.F3) :=
  ((List.finRange D).take i).filterMap (slot m shifts Q side v a)

@[simp] theorem prefixSlots_zero {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    prefixSlots m shifts Q side v a 0=[] := rfl

@[simp] theorem prefixSlots_full {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    prefixSlots m shifts Q side v a D=slots m shifts Q side v a := by
  have ht : (List.finRange D).take D=List.finRange D :=
    List.take_of_length_le (by simp)
  simp only [prefixSlots,slots,ht]

theorem prefixSlots_succ {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i : ℕ) (hi : i < D) :
    prefixSlots m shifts Q side v a (i+1)=prefixSlots m shifts Q side v a i ++
      (slot m shifts Q side v a ⟨i,hi⟩).toList := by
  unfold prefixSlots
  rw [List.take_succ_eq_append_getElem (by simpa using hi)]
  simp
  cases hs : slot m shifts Q side v a ⟨i,hi⟩ <;> simp [hs]

theorem rowPayload_append {m : ℕ} (b : ℕ) (xs ys : List (Fin m × SparseCode.F3)) :
    rowPayload b m (xs++ys)=rowPayload b m xs++rowPayload b m ys := by
  simp [rowPayload,List.flatten_append]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
