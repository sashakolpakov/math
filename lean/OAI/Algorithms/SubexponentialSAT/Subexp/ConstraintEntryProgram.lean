import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryScalar
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryCompare
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryExecution

namespace OAI.Algorithms

/-! Actual entries of the local defect matrix. The matrix service evaluates
the zero-extended joint entry, a preserving comparison computes the diagonal
bit, and the scalar service performs the subtraction. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryProgram

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

abbrev Data := State 10 46

def entryPorts : Fin 42 → Fin 46 := Fin.castAdd 4
def scalarRegisters : Fin 8 → Fin 10 := Fin.castAdd 2
def scalarPorts : Fin 10 → Fin 46 := ![0, 1, 2, 3, 4, 29, 6, 7, 8, 30]

theorem entryPorts_injective : Function.Injective entryPorts := Fin.castAdd_injective _ _
theorem scalarRegisters_injective : Function.Injective scalarRegisters := Fin.castAdd_injective _ _
theorem scalarPorts_injective : Function.Injective scalarPorts := by decide

abbrev entry : Cmd 10 46 := .call
  (ProgramLinking.liftProgram MatrixExtendedEntryProgram.program id entryPorts)
abbrev compare : Cmd 10 46 := .call ConstraintEntryCompare.program
abbrev subtract : Cmd 10 46 := .call
  (ProgramLinking.liftProgram ConstraintEntryScalar.program scalarRegisters scalarPorts)
abbrev command : Cmd 10 46 := .seq entry (.seq compare subtract)
def program := compiled command 23 0

variable {r Q Δ : ℕ}

def input (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (regs : Fin 10 → Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 42 then
    (MatrixExtendedEntryProgram.typedInput p i t u y xs regs).stacks ⟨j.val, h⟩ else []⟩

def output (base : Data) (regs : Fin 10 → Bool) (answer : List Bool) : Data :=
  ⟨regs, Function.update base.stacks 0 answer⟩

def value (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) : ZMod p :=
  (if u = y then 1 else 0) - MatrixExtendedEntryProgram.value p i t u y xs

def programBudget (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) : ℕ :=
  MatrixExtendedEntryProgram.programBudget p i t u y xs +
    27 * CollisionProgram.typeWidth r Q Δ + 13000 * (width p + 1)^2 + 36

theorem project_input (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (regs : Fin 10 → Bool) :
    projectState id entryPorts (input p i t u y xs regs) =
      MatrixExtendedEntryProgram.typedInput p i t u y xs regs := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    simp [input, entryPorts, j.isLt]
    rfl

theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (regs : Fin 10 → Bool) :
    ∃ out, RunsIn program (programBudget p i t u y xs)
      ((input p i t u y xs regs).withPC (some program.entry))
      ((output (input p i t u y xs regs) out (word p (value p i t u y xs))).withPC none) := by
  let base := input p i t u y xs regs
  let small := MatrixExtendedEntryProgram.typedInput p i t u y xs regs
  let x := MatrixExtendedEntryProgram.value p i t u y xs
  have hp : projectState id entryPorts base = small := project_input p i t u y xs regs
  have hbase : Function.extend entryPorts small.stacks base.stacks = base.stacks := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id entryPorts base Function.injective_id entryPorts_injective)
    rw [hp] at h
    exact h
  obtain ⟨er, ne, hne, te⟩ := MatrixExtendedEntryProgram.program_runsIn p h2 i t u y xs regs
  have te' : Trace MatrixExtendedEntryProgram.program ne
      ((projectState id entryPorts base).withPC
        (some MatrixExtendedEntryProgram.program.entry))
      ((MatrixExtendedEntryProgram.output small er (word p x)).withPC none) := by
    simpa only [hp] using te
  have he := eval_call_from_state MatrixExtendedEntryProgram.program id entryPorts base
    Function.injective_id entryPorts_injective te'
  let b := output base er (word p x)
  have heb : embedState id entryPorts base
      (MatrixExtendedEntryProgram.output small er (word p x)) = b := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [MatrixExtendedEntryProgram.output]
    · change Function.extend entryPorts (Function.update small.stacks 0 (word p x)) base.stacks = _
      rw [ProgramLinking.extend_update entryPorts_injective, hbase]
      rfl
  change Eval entry ne base
    (embedState id entryPorts base (MatrixExtendedEntryProgram.output small er (word p x))) at he
  rw [heb] at he
  obtain ⟨cr, ⟨nc, hnc, tc⟩, hc⟩ := ConstraintEntryCompare.program_runsIn b
    (by rfl) (by rfl) (by rfl) (by rfl)
  let c : Data := ⟨cr, b.stacks⟩
  have hcomp : Eval compare nc b c := .call _ tc
  let sr := cr ∘ scalarRegisters
  have hscalar : projectState scalarRegisters scalarPorts c =
      ConstraintEntryScalar.state p sr x [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> rfl
  have hb23 : b.stacks 23 = CollisionProgram.encodeType u := rfl
  have hb24 : b.stacks 24 = CollisionProgram.encodeType y := rfl
  have hdiag : sr 7 = decide (u = y) := by
    change cr 7 = decide (u = y)
    simpa only [hb23, hb24, CollisionProgram.encodeType_eq_iff] using hc
  have hvalue : ConstraintEntryScalar.result p (sr 7) x = value p i t u y xs := by
    rw [hdiag]
    simp [ConstraintEntryScalar.result, value, x]
  obtain ⟨rr, ns, hns, ts⟩ := ConstraintEntryScalar.program_runsIn p sr x
  rw [hvalue, ← hscalar] at ts
  have hs := eval_call_from_state ConstraintEntryScalar.program scalarRegisters scalarPorts c
    scalarRegisters_injective scalarPorts_injective ts
  let last := embedState scalarRegisters scalarPorts c
    (ConstraintEntryScalar.state p rr (value p i t u y xs) [])
  have hlocal : (ConstraintEntryScalar.state p rr (value p i t u y xs) []).stacks =
      Function.update (projectState scalarRegisters scalarPorts c).stacks 0
        (word p (value p i t u y xs)) := by
    rw [hscalar]
    funext j
    by_cases hj : j = 0
    · subst j; simp [ConstraintEntryScalar.state]
    · simp [ConstraintEntryScalar.state, hj]
  have hcbase : Function.extend scalarPorts
      (projectState scalarRegisters scalarPorts c).stacks c.stacks = c.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project scalarRegisters scalarPorts c
        scalarRegisters_injective scalarPorts_injective)
  have hlast : last = output base last.regs (word p (value p i t u y xs)) := by
    apply congrArg (StructuredProgram.State.mk last.regs)
    rw [hlocal, ProgramLinking.extend_update scalarPorts_injective, hcbase]
    simp [scalarPorts, c, b, output]
  change Eval subtract ns c last at hs
  rw [hlast] at hs
  have ht := he.seq (hcomp.seq hs)
  have h23 : (b.stacks 23).length = CollisionProgram.typeWidth r Q Δ := by
    rw [hb23, CollisionProgram.encodeType_length]
  have h24 : (b.stacks 24).length = CollisionProgram.typeWidth r Q Δ := by
    rw [hb24, CollisionProgram.encodeType_length]
  rw [h23, h24] at hnc
  refine ⟨last.regs, ne + (nc + ns) + 1, ?_, compiled_halt_trace ht 23 0⟩
  dsimp [programBudget]
  omega

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (regs : Fin 10 → Bool) :
    ∃ out, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * programBudget p i t u y xs)
      (BitProgram.primitiveCfg program ((input p i t u y xs regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((output (input p i t u y xs regs) out (word p (value p i t u y xs))).withPC none)) := by
  obtain ⟨out, hr⟩ := program_runsIn p h2 i t u y xs regs
  exact ⟨out, BitProgram.primitive_execution _ hr⟩

end SubexponentialSAT.Subexp.ConstraintEntryProgram

end OAI.Algorithms
