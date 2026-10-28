import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramFlatEmbed

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flatten_eval (regs : Fin 4 → Bool) (words : List (List Bool)) (mask forward : List Bool) :
    ∃ n rf, n ≤ 9*words.flatten.length+6*words.length+7 ∧ Eval flattenStep n
      (state regs (ProgramEncoding.encodeRecords words) mask forward []
        (ProgramEncoding.encodeRecords words) [] [] [] [] [])
      (state rf (ProgramEncoding.encodeRecords words) mask forward [] [] [] words.flatten [] [] []) := by
  let a := flatInitial regs words mask forward
  let count := 9*(words.map List.length).sum+6*words.length+7
  have raw := SubexponentialSAT.Subexp.AssignmentRecordViews.flatten_trace (regs 0) (regs 1) (regs 2) words [] []
  have hproject := flat_project regs words mask forward
  have ht := Eq.mp (congrArg (fun start : State 3 3 =>
    Trace SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram count
      (start.withPC (some SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram.entry))
      ((SubexponentialSAT.Subexp.AssignmentRecordViews.data false false false [] []
        (words.flatten ++ [])).withPC none)) hproject.symm) raw
  have he := eval_call_from_state SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram
    flatRegs flatStacks a (Fin.castAdd_injective 3 1) (by decide) ht
  let rout := flatOutRegs regs
  have hb := flat_embed regs words mask forward
  refine ⟨count,rout,?_,Eq.mp (congrArg (fun b : Data => Eval flattenStep count a b) hb) he⟩
  dsimp [count]
  rw [List.length_flatten]

end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
