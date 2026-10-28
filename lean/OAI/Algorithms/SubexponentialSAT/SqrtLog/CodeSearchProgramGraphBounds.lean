import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphPrepare

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem scalarFrames_binary_length (xs : List (ZMod 2)) :
    (scalarFrames xs).length = 5 * xs.length := by
  rw [scalarFrames_binary,framedCellStream_length,List.length_map]

theorem matrixFrames_binary_length {D r : ℕ} (s : Fin D → Cayley.Cube r) :
    (matrixFrames s).length = 5 * (D * r) := by
  rw [← framedMatrix_eq_matrixFrames,framedMatrix,framedVector_eq_scalarFrames,
    scalarFrames_binary_length,List.length_ofFn]

def graphInputSpan (D r qlen Dlen : ℕ) := 5 * (D * r) + 5 * r + D + qlen + Dlen + 5

theorem graphInput_length_le {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (regs : Fin 8 → Bool) (qbits Dbits : List Bool) (i : Fin 18) :
    ((extendPairState (matrixInput s x regs) qbits Dbits).stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length := by
  have hm := matrixFrames_binary_length s
  have hx := scalarFrames_binary_length (List.ofFn x)
  simp only [List.length_ofFn] at hx
  have h16 : (16 : Fin 18).val = 16 := rfl
  have h17 : (17 : Fin 18).val = 17 := rfl
  fin_cases i <;>
    norm_num [extendPairState,matrixInput,MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
      modulus_two,zero_two,graphInputSpan,hm,hx,Fin.ext_iff,h16,h17] <;> omega

theorem preparedGraphWord_length_le {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState)
    (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits)
    (hD : a.stacks 32 = Dbits) (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse)
    (i : Fin 29) :
    ((projectState id graphWordStacks (preparedGraphWord a)).stacks i).length ≤
      graphInputSpan D r qbits.length Dbits.length := by
  by_cases hi : i.val < 18
  · let j : Fin 18 := ⟨i.val,hi⟩
    have hij : graphCountStacks j = i := Fin.ext rfl
    have hp := congrArg (fun b : State 8 18 => (b.stacks j).length)
      (preparedGraphWord_project s x qbits Dbits a he hm ht hq hD hx)
    change ((projectState id graphWordStacks (preparedGraphWord a)).stacks (graphCountStacks j)).length = _ at hp
    rw [hij] at hp
    rw [hp]
    exact graphInput_length_le s x _ qbits Dbits j
  · rw [preparedGraphWord_scratch a he i (by omega)]
    exact Nat.zero_le _

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
