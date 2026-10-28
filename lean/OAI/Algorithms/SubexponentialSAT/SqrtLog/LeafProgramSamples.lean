import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

namespace OAI.Algorithms

/-! The actual indexed node sampler, including the paid handoff between ring
setup's readout aliases and the node worker's reusable cache bank. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Samples
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def prepare : Code := .seq (LeafAssignmentSetupProgram.clear 190)
  (LeafAssignmentSetupProgram.clear 191)
def prepared (a : Data) : Data :=
  LeafAssignmentSetupProgram.cleared (LeafAssignmentSetupProgram.cleared a 190) 191
def prepareCost (a : Data) : ℕ :=
  2*(a.stacks 190).length+2*(a.stacks 191).length+6

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) := by
  have h1 := LeafAssignmentSetupProgram.clear_eval a 190
  have h2 := LeafAssignmentSetupProgram.clear_eval (LeafAssignmentSetupProgram.cleared a 190) 191
  have hlen : (LeafAssignmentSetupProgram.cleared a 190).stacks 191 = a.stacks 191 := by
    simp [LeafAssignmentSetupProgram.cleared]
  rw [hlen] at h2
  convert h1.seq h2 using 1 <;> first | rfl | (unfold prepareCost; omega)

theorem prepared_stacks (a : Data) :
    (prepared a).stacks = Function.update (Function.update a.stacks 190 []) 191 [] := rfl

theorem prepared_frame (a : Data) (i : Fin 768) (h190 : i ≠ 190) (h191 : i ≠ 191) :
    (prepared a).stacks i = a.stacks i := by
  simp [prepared_stacks,h190,h191]

def command : Code := .seq prepare (.call (LeafNodeSamplesProgram.collectProgram Node.command))
def program := compiled command 300 265

end SubexponentialSAT.SqrtLog.LeafProgram.Samples

end
end OAI.Algorithms
