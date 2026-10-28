import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

/-- Closed scalar operation count for one local row. -/
def explicitRowCost (r D b Ld Lm : ℕ) : ℕ :=
  7*D+35*(D*r)+D*(2000*(r+Ld+Lm+b+D+4)^2+2)+2*D+4*(D*b)+23

/-- Closed complete program bound, including source copies and final cleanup. -/
def explicitCost (r D t b Ld Lm : ℕ) : ℕ :=
  2^r*(2*(35*(t*D)+7*t+t*(explicitRowCost r D b Ld Lm+2)+13)+8*r+10)+13*r+18

theorem binary_matrixFrames_length {r D : ℕ} (shifts : Fin D → Cayley.Cube r) :
    (CodeSearchProgram.matrixFrames shifts).length=5*(D*r) := by
  rw [matrixFrames_shifts]
  simp [shiftRows,Shift.frames,Cell.frame,List.length_flatMap,Function.comp_def,
    vertexBits,List.sum_replicate,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem cost_eq_explicit {r D t : ℕ} (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) :
    cost dword mword width shifts Q=
      explicitCost r D t width.length dword.length mword.length := by
  simp [cost,vertexCost,sideCost,rowCost,portWidth,initialStacks,inputState,
    binary_matrixFrames_length,ternary_matrixFrames_length,explicitCost,explicitRowCost]
  ring

theorem program_runsIn_explicit {r D t m : ℕ} (regs : Fin 16 → Bool)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hd : SubexponentialSAT.BinaryArithmetic.toNat dword=D) (hm : SubexponentialSAT.BinaryArithmetic.toNat mword=m)
    (hcap : 3*m ≤ 2^width.length) :
    ∃ rf, SubexponentialSAT.BitProgram.RunsIn program
      (explicitCost r D t width.length dword.length mword.length)
      ((inputState regs dword mword width shifts Q).withPC (some program.entry))
      ((outputState (m:=m) rf dword mword width shifts Q).withPC none) := by
  simpa only [cost_eq_explicit] using program_runsIn regs dword mword width shifts Q hd hm hcap


theorem program_primitive_runsIn {r D t m : ℕ} (regs : Fin 16 → Bool)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hd : SubexponentialSAT.BinaryArithmetic.toNat dword=D) (hm : SubexponentialSAT.BinaryArithmetic.toNat mword=m)
    (hcap : 3*m ≤ 2^width.length) :
    ∃ rf, Computation.RunsIn (SubexponentialSAT.BitProgram.primitive program).step
      (SubexponentialSAT.BitProgram.primitiveOverhead program *
        explicitCost r D t width.length dword.length mword.length)
      (SubexponentialSAT.BitProgram.primitiveCfg program
        ((inputState regs dword mword width shifts Q).withPC (some program.entry)))
      (SubexponentialSAT.BitProgram.primitiveCfg program
        ((outputState (m:=m) rf dword mword width shifts Q).withPC none)) := by
  obtain ⟨rf,he⟩ := program_runsIn_explicit regs dword mword width shifts Q hd hm hcap
  exact ⟨rf,SubexponentialSAT.BitProgram.primitive_execution program he⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
