import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramFrame
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram

namespace OAI.Algorithms

/-! Native alphabet/seed construction followed by actual assignment copying.
The old producer is used at delta=0 so the seed count is exactly ambient+factors;
the new scorer's four-word depth is installed separately. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def context (r Q n f : ℕ) (pairs : List Bool) :=
  AssignmentInputProgram.context r Q 0 n f pairs

def core : Code :=
  .seq (.call (ProgramLinking.liftProgram AssignmentInputProgram.program id lowPorts))
    (.call (ProgramLinking.liftProgram AssignmentInitProgram.program id lowPorts))

def coreBudget (r Q n f : ℕ) (pairs : List Bool) : ℕ :=
  AssignmentInputProgram.budget r Q 0 n f pairs+1+
    AssignmentInitProgram.sourceCost (context r Q n f pairs)

/-- Actual generation from numeric parameters and the installed raw pair
bytes. No alphabet, seed list, or initialized assignment is an input. -/
theorem core_eval (outside : Store) (regs : Fin 16 → Bool)
    (r Q n f : ℕ) (pairs : List Bool) (hr : 0 < r) :
    ∃ t ≤ coreBudget r Q n f pairs, Eval core t
      (framed outside (AssignmentInputProgram.inputState regs r Q 0 n f pairs))
      (framed outside (AssignmentInitProgram.outputState (context r Q n f pairs))) := by
  obtain ⟨t,ht,he⟩ := AssignmentInputProgram.program_runsIn regs r Q 0 n f pairs hr
  have h1 := framed_call AssignmentInputProgram.program outside he
  have h2 := framed_call AssignmentInitProgram.program outside
    (AssignmentInitProgram.program_trace (context r Q n f pairs) (fun _ => false))
  exact ⟨t+AssignmentInitProgram.sourceCost (context r Q n f pairs),
    Nat.add_le_add_right ht _, h1.seq h2⟩

def extent (r Q n f : ℕ) (pairs : List Bool) :=
  AssignmentInputProgram.extent r Q 0 n f pairs

theorem coreBudget_polynomial (r Q n f : ℕ) (pairs : List Bool) (hr : 0 < r) :
    coreBudget r Q n f pairs ≤ 21000*(extent r Q n f pairs+1)^4 := by
  have ha := AssignmentInputProgram.budget_le r Q 0 n f pairs hr
  have hb := AssignmentInitProgram.sourceCost_le (context r Q n f pairs)
    (extent r Q n f pairs)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
  change _ ≤ 20000*(extent r Q n f pairs+1)^4 at ha
  unfold coreBudget
  have hp : 1 ≤ extent r Q n f pairs+1 := by omega
  have hs : (extent r Q n f pairs+1)^2 ≤ (extent r Q n f pairs+1)^4 :=
    Nat.pow_le_pow_right hp (by decide)
  have hf : 1 ≤ (extent r Q n f pairs+1)^4 := one_le_pow₀ hp
  omega

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
