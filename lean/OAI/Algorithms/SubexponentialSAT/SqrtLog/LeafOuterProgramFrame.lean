import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSelect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramHashParameters

namespace OAI.Algorithms

/-! Literal frame facts needed between hash selection and the final query. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

private theorem selector_val (j : Fin 14) :
    (LeafProgram.HashParameters.ports.hash.stack j).val=768+j.val := by
  fin_cases j <;> rfl

theorem selected_worker_empty {a b : Data} (hw : WorkerEmpty a)
    (hf : Execution.Hash.ContextFrame LeafProgram.HashParameters.ports.hash a b) :
    WorkerEmpty b := by
  intro i
  rw [hf.1 (workerStack i) (by
    intro j he
    have hv:=congrArg Fin.val he
    have hj:=selector_val j
    change (LeafProgram.HashParameters.ports.hash.stack j).val=i.val at hv
    have:=i.isLt
    omega)]
  exact hw i

theorem selected_outer_frame {a b : Data}
    (hf : Execution.Hash.ContextFrame LeafProgram.HashParameters.ports.hash a b)
    (i : Fin 896) (hi : 782 ≤ i.val) : b.stacks i=a.stacks i := by
  apply hf.1 i
  intro j he
  have hv:=congrArg Fin.val he
  have hj:=selector_val j
  have:=j.isLt
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
