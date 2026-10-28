import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem FrontState.protected_frame {q : LeafQueryFrontend.Query} {k : ℕ} {a b : Data}
    {l : Fin 8 → ℕ} {w : Bank.Words} (h : FrontState q k a b l w)
    (i : Fin 768) (hi : Protected i) : b.stacks i=a.stacks i := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
  all_goals apply h.frame
  all_goals try { first | decide | (right; omega) }
  all_goals try { intro he; have hv := congrArg Fin.val he; norm_num at hv; omega }
  all_goals intro j he
  all_goals have hv := congrArg Fin.val he
  all_goals fin_cases j <;> simp [Exports.destination] at hv <;> omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
