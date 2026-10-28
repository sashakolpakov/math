import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramMask
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def flatInitial (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) : Data :=
  state regs (ProgramEncoding.encodeRecords words) mask forward []
    (ProgramEncoding.encodeRecords words) [] [] [] [] []
def flatOutRegs (regs : Fin 4 → Bool) : Fin 4 → Bool := ![false,false,false,regs 3]

theorem flat_project (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) : projectState flatRegs flatStacks (flatInitial regs words mask forward) =
    SubexponentialSAT.Subexp.AssignmentRecordViews.data (regs 0) (regs 1) (regs 2)
      (ProgramEncoding.encodeRecords words ++ []) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;>
      simp [flatInitial,flatStacks,state,tapes]


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
