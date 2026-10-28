import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowInputSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionVectorExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchTypes
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDelta
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowRearrange
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceProgram

namespace OAI.Algorithms

/-! The fixed global source-row command.  Input preparation, every matrix
entry, position selection, delta comparison, cache copies, source emission,
and final workspace cleanup are executable subcommands. -/

namespace SubexponentialSAT.Subexp.UniversalRowAssembly

open BitProgram StructuredCalls StackRoutines
open UniversalRowWorkspace (port)

abbrev Data := State 16 288
abbrev Code := Cmd 16 288

def nativeRegs : Fin 10 → Fin 16 := Fin.castAdd 6
theorem nativeRegs_injective : Function.Injective nativeRegs := Fin.castAdd_injective 10 6

def vector : Code := .call (ProgramLinking.liftProgram
  CorrectionVectorProgram.program nativeRegs port)

def mismatchProgram := compiled UniversalRowMismatchTypes.command (23 : Fin 49) 45
def mismatch : Code := .call (ProgramLinking.liftProgram mismatchProgram nativeRegs port)

def loadOne : Code := .call (copyProgram 132 (port 44) (port 15) (0 : Fin 16) 1)

def deltaProgram := compiled UniversalRowDelta.command (23 : Fin 49) 18
def delta : Code := .call (ProgramLinking.liftProgram deltaProgram nativeRegs port)

def rowRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def rowPorts : Fin 32 → Fin 288 := fun j => port (j.castAdd 17)
theorem rowRegs_injective : Function.Injective rowRegs := Fin.castAdd_injective 8 8
theorem rowPorts_injective : Function.Injective rowPorts :=
  UniversalRowWorkspace.port_injective.comp (Fin.castAdd_injective 32 17)

def emit : Code := .call (ProgramLinking.liftProgram
  UniversalRowSourceProgram.program rowRegs rowPorts)

def command : Code :=
  .seq UniversalRowInputSetup.command
    (.seq vector (.seq mismatch (.seq loadOne (.seq delta
      (.seq UniversalRowRearrange.command (.seq emit UniversalRowWorkspace.command))))))

abbrev program : Program 16 288 (size command + 1) := compiled command 272 26

/-- The global dispatcher has nine additional registers. Its high metadata
flags are outside this actual fixed subroutine call. -/
abbrev callerCommand : Cmd 25 288 :=
  .call (ProgramLinking.liftProgram program (Fin.castAdd 9) id)

private theorem extend_project_stacks {r s : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin 288) (a : Data)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    Function.extend stack (projectState register stack a).stacks a.stacks = a.stacks :=
  congrArg StructuredProgram.State.stacks (embedState_project register stack a hr hs)

theorem vector_eval {r Q Δ : ℕ} (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))
    (constant shape : List Bool) (a : Data)
    (hcw : constant.length = MatrixWordEncoding.width p)
    (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * MatrixWordEncoding.width p)
    (hin : projectState nativeRegs port a =
      CorrectionVectorProgram.input p i u y xs constant shape (a.regs ∘ nativeRegs)) :
    ∃ n ≤ CorrectionVectorProgram.programBudget p i u y xs, ∃ b : Data,
      Eval vector n a b ∧ b.stacks = Function.update a.stacks (port 48)
        (CorrectionVectorProgram.vector p i u y xs 0 Q) := by
  obtain ⟨rf, n, hn, ht⟩ := CorrectionVectorProgram.program_runsIn p i u y xs h2 constant shape
    hcw hcv hsw (a.regs ∘ nativeRegs)
  let last := CorrectionVectorProgram.finished p i u y xs constant shape rf
  have hlast : last.stacks = Function.update (projectState nativeRegs port a).stacks 48
      (CorrectionVectorProgram.vector p i u y xs 0 Q) := by
    rw [hin]
    rfl
  have ht' : Trace CorrectionVectorProgram.program n
      ((projectState nativeRegs port a).withPC (some CorrectionVectorProgram.program.entry))
      (last.withPC none) := by simpa only [hin] using ht
  let b := embedState nativeRegs port a last
  have he := eval_call_from_state CorrectionVectorProgram.program nativeRegs port a
    nativeRegs_injective UniversalRowWorkspace.port_injective ht'
  refine ⟨n, hn, b, he, ?_⟩
  change Function.extend port last.stacks a.stacks = _
  rw [hlast, ProgramLinking.extend_update UniversalRowWorkspace.port_injective,
    extend_project_stacks nativeRegs port a nativeRegs_injective UniversalRowWorkspace.port_injective]

theorem mismatch_eval {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (a : Data)
    (hin : UniversalRowMismatchTypes.InputReady i u y (projectState nativeRegs port a))
    (h45 : a.stacks (port 45) = []) :
    ∃ n ≤ UniversalRowMismatchTypes.extractBudget (r := r) (Q := Q) i +
        UniversalRowMismatchProgram.budget Q r + 8 * (Q * r) + 13,
      ∃ b : Data, Eval mismatch n a b ∧ b.stacks = Function.update a.stacks (port 45)
        (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
          (MismatchPlanProgram.selectedPositions y.head (u.slot i)).reverse)) := by
  obtain ⟨n, hn, last, ht, hs⟩ := UniversalRowMismatchTypes.command_eval i u y
    (projectState nativeRegs port a) hin h45
  let b := embedState nativeRegs port a last
  have he := eval_call_from_state mismatchProgram nativeRegs port a
    nativeRegs_injective UniversalRowWorkspace.port_injective
    (compiled_halt_trace ht (23 : Fin 49) 45)
  refine ⟨n + 1, by omega, b, he, ?_⟩
  change Function.extend port last.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update UniversalRowWorkspace.port_injective,
    extend_project_stacks nativeRegs port a nativeRegs_injective UniversalRowWorkspace.port_injective]

theorem loadOne_eval (a : Data) (h44 : a.stacks (port 44) = [])
    (h15 : a.stacks (port 15) = []) :
    ∃ b : Data, Eval loadOne (7 * (a.stacks 132).length + 5) a b ∧
      b.stacks = Function.update a.stacks (port 44) (a.stacks 132) := by
  have h := TupleProgram.copy_eval (132 : Fin 288) (port 44) (port 15) (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) a h15
  refine ⟨_, h, ?_⟩
  simp [copyStacks, h44]

theorem delta_eval {r Q Δ : ℕ} (u y : MulticolorTypes.UniversalType r Q Δ)
    (zero one : List Bool) (a : Data)
    (hu : a.stacks (port 23) = CollisionProgram.encodeType u)
    (hy : a.stacks (port 24) = CollisionProgram.encodeType y)
    (hz : a.stacks (port 47) = zero) (ho : a.stacks (port 44) = one)
    (h18 : a.stacks (port 18) = []) (h15 : a.stacks (port 15) = []) :
    ∃ n ≤ 13 * CollisionProgram.typeWidth r Q Δ +
        7 * (if u = y then one else zero).length + 28,
      ∃ b : Data, Eval delta n a b ∧
        b.stacks = Function.update (Function.update (Function.update a.stacks
          (port 23) []) (port 24) []) (port 18) (if u = y then one else zero) := by
  obtain ⟨n, hn, last, ht, hs⟩ := UniversalRowDelta.typed_command_eval u y zero one
    (projectState nativeRegs port a) hu hy hz ho h18 h15
  let b := embedState nativeRegs port a last
  have he := eval_call_from_state deltaProgram nativeRegs port a
    nativeRegs_injective UniversalRowWorkspace.port_injective
    (compiled_halt_trace ht (23 : Fin 49) 18)
  refine ⟨n + 1, by omega, b, he, ?_⟩
  change Function.extend port last.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update UniversalRowWorkspace.port_injective,
    ProgramLinking.extend_update UniversalRowWorkspace.port_injective,
    ProgramLinking.extend_update UniversalRowWorkspace.port_injective,
    extend_project_stacks nativeRegs port a nativeRegs_injective UniversalRowWorkspace.port_injective]

theorem emit_eval (t : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid t width rowWidth positions)
    (delta limit zero one : List Bool) (a : Data)
    (ha : UniversalRowLoop.ready t width rowWidth positions (projectState rowRegs rowPorts a))
    (hd : a.stacks (port 18) = delta) (hl : a.stacks (port 13) = limit)
    (hz : a.stacks (port 3) = zero) (ho : a.stacks (port 10) = one)
    (h14 : a.stacks (port 14) = []) (h17 : a.stacks (port 17) = [])
    (h31 : a.stacks (port 31) = []) :
    ∃ n ≤ UniversalRowSourceProgram.bound t width rowWidth positions delta limit zero one,
      ∃ b : Data, Eval emit n a b ∧
        b.stacks = Function.update (Function.update a.stacks (port 18) []) (port 31)
          (UniversalRowProgram.rowCode zero one (zero ++ one)
            (UniversalRowDataProgram.row t positions delta limit)) := by
  obtain ⟨last, ⟨n, hn, ht⟩, hs⟩ := UniversalRowSourceProgram.program_runsIn t width rowWidth
    positions valid delta limit zero one (projectState rowRegs rowPorts a) ha hd hl hz ho h14 h17 h31
  let b := embedState rowRegs rowPorts a last
  have he := eval_call_from_state UniversalRowSourceProgram.program rowRegs rowPorts a
    rowRegs_injective rowPorts_injective ht
  refine ⟨n, hn, b, he, ?_⟩
  change Function.extend rowPorts last.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update rowPorts_injective,
    ProgramLinking.extend_update rowPorts_injective,
    extend_project_stacks rowRegs rowPorts a rowRegs_injective rowPorts_injective]
  rfl

end SubexponentialSAT.Subexp.UniversalRowAssembly

end OAI.Algorithms
