import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRepresentation

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

def vertexBits {r : ℕ} (v : Cayley.Cube r) : List Bool :=
  List.ofFn fun i => decide (v i=1)

@[simp] theorem vertexBits_length {r : ℕ} (v : Cayley.Cube r) :
    (vertexBits v).length=r := List.length_ofFn

theorem toNat_ofFn {r : ℕ} (f : Fin r → Bool) :
    BinaryArithmetic.toNat (List.ofFn f)=∑ i : Fin r,bitVal (f i)*2^i.val := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ,toNat_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem vertexBits_value {r : ℕ} (v : Cayley.Cube r) :
    BinaryArithmetic.toNat (vertexBits v)=((WalshExistence.cubeEquiv r).symm v).val := by
  rw [vertexBits,toNat_ofFn,WalshExistence.cubeEquiv_encode]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hb (x : ZMod 2) : bitVal (decide (x=1))=x.val := by fin_cases x <;> decide
  exact hb (v i)

theorem binary_scalarWord (x : ZMod 2) :
    SubexponentialSAT.Subexp.MatrixWordEncoding.word 2 x=[decide (x=1),false] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 2=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem vertexFrames {r : ℕ} (v : Cayley.Cube r) :
    CodeSearchProgram.scalarFrames (List.ofFn v)=Shift.frames (vertexBits v) := by
  simp only [CodeSearchProgram.scalarFrames,CodeSearchProgram.words_eq_flatMap,vertexBits,Shift.frames,List.flatMap,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [binary_scalarWord]
  rfl

theorem shifted_vertexBits {r : ℕ} (side : Bool) (v s : Cayley.Cube r) :
    Shift.result side (List.ofFn fun i => (decide (v i=1),decide (s i=1))) =
      vertexBits (if side then v+s else v) := by
  simp only [Shift.result,List.map_ofFn,vertexBits,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  cases side
  · rfl
  · have hb (x y : ZMod 2) : (decide (x=1)).xor (decide (y=1))=decide (x+y=1) := by
      fin_cases x <;> fin_cases y <;> decide
    exact hb (v i) (s i)

theorem shift_program_vertex {r : ℕ} (v s : Cayley.Cube r) (side : Bool)
    (regs : Fin 8 → Bool) (hside : regs 7=side) (tail : List Bool) :
    ∃ rf, rf 7=side ∧ SubexponentialSAT.BitProgram.RunsIn Shift.program (14*r+6)
      ((Shift.state regs (CodeSearchProgram.scalarFrames (List.ofFn s)++tail)
        (vertexBits v) [] []).withPC (some Shift.program.entry))
      ((Shift.state rf tail [] [] (vertexBits (if side then v+s else v))).withPC none) := by
  have h := Shift.program_runsIn
    (List.ofFn fun i => (decide (v i=1),decide (s i=1))) side regs hside tail
  simpa [List.map_ofFn,vertexBits,vertexFrames,shifted_vertexBits,Function.comp_def] using h

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
