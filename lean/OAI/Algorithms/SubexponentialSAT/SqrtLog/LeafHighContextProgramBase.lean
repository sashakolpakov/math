import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramShift
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

abbrev Data := State 4 10
abbrev Code := Cmd 4 10

def tapes (counter mask forward output copy acc high work tmp low : List Bool) : Fin 10 → List Bool :=
  fun i => match i.val with
  | 0 => counter
  | 1 => mask
  | 2 => forward
  | 3 => output
  | 4 => copy
  | 5 => acc
  | 6 => high
  | 7 => work
  | 8 => tmp
  | _ => low
def state (regs : Fin 4 → Bool) (counter mask forward output copy acc high work tmp low : List Bool) : Data :=
  ⟨regs,tapes counter mask forward output copy acc high work tmp low⟩

def maskRegs : Fin 2 → Fin 4 := Fin.castAdd 2
def maskStacks : Fin 4 → Fin 10 := ![1,7,2,8]
def flatRegs : Fin 3 → Fin 4 := Fin.castAdd 1
def flatStacks : Fin 3 → Fin 10 := ![4,5,6]
def mergeStacks : Fin 4 → Fin 10 := ![7,6,9,3]

def maskStep : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Mask.program maskRegs maskStacks)
def copyCounter : Code := .call (StackRoutines.copyProgram 0 4 8 0 1)
def flattenStep : Code := .call (ProgramLinking.liftProgram SubexponentialSAT.Subexp.AssignmentRecordViews.flattenProgram flatRegs flatStacks)
def copyMask : Code := .call (StackRoutines.copyProgram 1 7 8 0 1)
def mergeStep : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Restriction.program id mergeStacks)
def command : Code := .seq maskStep (.seq copyCounter (.seq flattenStep (.seq copyMask mergeStep)))
def program := compiled command 0 3

/-- Transport only a caller's initial state; do not rewrite through its program. -/
theorem transport_initial {r s l : ℕ} (p : Program r s l) (bound : ℕ)
    {a b final : State r s} (hab : a = b)
    (h : RunsIn p bound (a.withPC (some p.entry)) (final.withPC none)) :
    RunsIn p bound (b.withPC (some p.entry)) (final.withPC none) := by
  cases hab
  exact h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
