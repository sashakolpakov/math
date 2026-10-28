import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramFlatPorts

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_embed_generic (regs : Fin 4 → Bool) (counter mask forward high : List Bool) :
    embedState flatRegs flatStacks (state regs counter mask forward [] counter [] [] [] [] [])
      (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high) =
    state (flatOutRegs regs) counter mask forward [] [] [] high [] [] [] := by
  exact embedState_eq_of_ports flatRegs flatStacks
    (state regs counter mask forward [] counter [] [] [] [] [])
    (state (flatOutRegs regs) counter mask forward [] [] [] high [] [] [])
    (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high)
    (Fin.castAdd_injective 3 1) flat_stack_injective
    (flat_reg_ports regs) (flat_reg_frame regs)
    (flat_stack_ports counter mask forward high) (flat_stack_frame counter mask forward high)

theorem flat_embed (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) :
    embedState flatRegs flatStacks (flatInitial regs words mask forward)
      (SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] (words.flatten ++ [])) =
    state (flatOutRegs regs) (ProgramEncoding.encodeRecords words) mask forward [] [] [] words.flatten [] [] [] := by
  have h := flat_embed_generic regs (ProgramEncoding.encodeRecords words) mask forward words.flatten
  have hs : SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] (words.flatten ++ []) =
      SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] words.flatten :=
    congrArg (fun high => SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] [] high)
      (List.append_nil words.flatten)
  exact (congrArg (embedState flatRegs flatStacks (flatInitial regs words mask forward)) hs).trans h

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
