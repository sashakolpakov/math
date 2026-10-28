import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSamples
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramWide

namespace OAI.Algorithms

/-! One high-assignment residual query. The high values are physically
extracted from the live odometer, all nodes are evaluated, and the native CRT
result is read as an integer. Only transient jets/high vectors are reclaimed
at exit; the per-mark ring and parked layout masters are reusable. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def finish : Code := .seq (LeafAssignmentSetupProgram.clear 265)
  (.seq (LeafAssignmentSetupProgram.clear 702) (LeafAssignmentSetupProgram.clear 703))
def finished (a : Data) : Data :=
  LeafAssignmentSetupProgram.cleared
    (LeafAssignmentSetupProgram.cleared (LeafAssignmentSetupProgram.cleared a 265) 702) 703
def finishCost (a : Data) : ℕ :=
  2*(a.stacks 265).length+2*(a.stacks 702).length+2*(a.stacks 703).length+9

theorem finish_eval (a : Data) : Eval finish (finishCost a) a (finished a) := by
  let b := LeafAssignmentSetupProgram.cleared a 265
  let c := LeafAssignmentSetupProgram.cleared b 702
  have h1 := LeafAssignmentSetupProgram.clear_eval a 265
  have h2 := LeafAssignmentSetupProgram.clear_eval b 702
  have h3 := LeafAssignmentSetupProgram.clear_eval c 703
  have hb : b.stacks 702 = a.stacks 702 := by simp [b,LeafAssignmentSetupProgram.cleared]
  have hc : c.stacks 703 = a.stacks 703 := by simp [c,b,LeafAssignmentSetupProgram.cleared]
  rw [hb] at h2
  rw [hc] at h3
  have he := h1.seq (h2.seq h3)
  change Eval finish (2*(a.stacks 265).length+3+
    (2*(a.stacks 702).length+3+(2*(a.stacks 703).length+3))) a (finished a) at he
  have hk : 2*(a.stacks 265).length+3+
      (2*(a.stacks 702).length+3+(2*(a.stacks 703).length+3)) = finishCost a := by
    unfold finishCost
    omega
  rw [hk] at he
  exact he

theorem finished_stacks (a : Data) : (finished a).stacks =
    Function.update (Function.update (Function.update a.stacks 265 []) 702 []) 703 [] := rfl

theorem finished_frame (a : Data) (i : Fin 768)
    (h265 : i ≠ 265) (h702 : i ≠ 702) (h703 : i ≠ 703) :
    (finished a).stacks i = a.stacks i := by
  simp only [finished_stacks,Function.update_of_ne h265,
    Function.update_of_ne h702,Function.update_of_ne h703]

def command : Code := .seq LeafHighContextProgram.command
  (.seq Samples.command (.seq Count.Prepare.command (.seq Count.command finish)))
def program := compiled command 330 323

/-- Exact sequential composition of the five concrete instruction tables.
The sample/CRT semantics are discharged by their native theorems at the
branch contract; no Boolean test replaces the numeric branch result. -/
theorem command_eval (a b c e : Data) (kh ks kc : ℕ)
    (hh : Eval LeafHighContextProgram.command kh a b)
    (hs : Eval Samples.command ks b c)
    (hc : Eval Count.command kc (Count.Prepare.output c) e) :
    Eval command (kh+(ks+(Count.Prepare.budget c+(kc+finishCost e)))) a (finished e) :=
  hh.seq (hs.seq ((Count.Prepare.command_eval c).seq (hc.seq (finish_eval e))))

end SubexponentialSAT.SqrtLog.LeafProgram.Residual

end
end OAI.Algorithms
