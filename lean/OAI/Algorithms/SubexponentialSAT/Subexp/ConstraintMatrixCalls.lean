import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixState

namespace OAI.Algorithms

/-! Concrete calls used by each slot iteration: physical Joint filtering
and physical evaluation of all corresponding constraint rows. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixProgram

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

theorem joint_eval (p : ℕ) [Fact p.Prime] (r Q Δ t g index : ℕ)
    (coefficients : List (ZMod p)) (regs : Fin 18 → Bool)
    (accumulator rowCount remaining : List Bool) :
    ∃ n ≤ TypeFiberProgram.budget true ⟨r, t, g, Q * r, index⟩
        (TypeEnumeration.sideBytes r Q Δ t g), ∃ out,
      Eval jointFilter n
        (state p r Q t g coefficients (TypeEnumeration.sideBytes r Q Δ t g)
          regs index [] accumulator rowCount remaining)
        (state p r Q t g coefficients (TypeEnumeration.sideBytes r Q Δ t g)
          out index (ProgramEncoding.encodeRecords (TypeEnumeration.jointBytes r Q Δ t g index))
          accumulator rowCount remaining) := by
  let side := TypeEnumeration.sideBytes r Q Δ t g
  let joints := ProgramEncoding.encodeRecords (TypeEnumeration.jointBytes r Q Δ t g index)
  let ctx : TypeFiberProgram.Context := ⟨r, t, g, Q * r, index⟩
  let a := state p r Q t g coefficients side regs index [] accumulator rowCount remaining
  have hp : projectState fiberRegisters fiberPorts a =
      TypeFiberProgram.inputState ctx side (regs ∘ fiberRegisters) :=
    project_fiber p r Q t g coefficients side regs index accumulator rowCount remaining
  obtain ⟨fr, n, hn, ht⟩ := TypeFiberProgram.joint_runsIn r Q Δ t g index (regs ∘ fiberRegisters)
  let smallOut := TypeFiberProgram.state ctx fr (ProgramEncoding.encodeRecords side) [] joints
  have ht' : Trace (TypeFiberProgram.program true) n
      ((projectState fiberRegisters fiberPorts a).withPC (some (TypeFiberProgram.program true).entry))
      (smallOut.withPC none) := by
    rw [hp]
    exact ht
  have he := eval_call_from_state (TypeFiberProgram.program true) fiberRegisters fiberPorts a
    fiberRegisters_injective fiberPorts_injective ht'
  let out := Function.extend fiberRegisters fr regs
  have hl : smallOut.stacks =
      Function.update (projectState fiberRegisters fiberPorts a).stacks 10 joints := by
    rw [hp]
    funext j
    fin_cases j <;> rfl
  have hb : Function.extend fiberPorts (projectState fiberRegisters fiberPorts a).stacks a.stacks =
      a.stacks := congrArg StructuredProgram.State.stacks
        (embedState_project fiberRegisters fiberPorts a fiberRegisters_injective fiberPorts_injective)
  have hend : embedState fiberRegisters fiberPorts a smallOut =
      state p r Q t g coefficients side out index joints accumulator rowCount remaining := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hl, ProgramLinking.extend_update fiberPorts_injective, hb]
      exact state_joint p r Q t g coefficients side regs index [] accumulator rowCount remaining joints
  exact ⟨n, hn, out, hend ▸ he⟩

variable {r Q Δ : ℕ}

theorem slot_eval (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (anchor : UniversalType r Q Δ)
    (coefficients : List (ZMod p)) (rows columns : List (UniversalType r Q Δ)) (E : ℕ)
    (hE : ∀ u ∈ rows, ∀ y ∈ columns, ConstraintEntryProgram.programBudget p i t u y coefficients ≤ E)
    (regs : Fin 18 → Bool) (accumulator rowCount remaining : List Bool) :
    ∃ n ≤ ConstraintMatrixSlot.budget p E columns.length
        (ProgramEncoding.encodeRecords (columns.map CollisionProgram.encodeType)).length
        rows.length r Q Δ, ∃ out,
      Eval emitSlot n
        (state p r Q t.val g.val coefficients (columns.map CollisionProgram.encodeType)
          regs i.val (ProgramEncoding.encodeRecords (rows.map CollisionProgram.encodeType))
          accumulator rowCount remaining)
        (state p r Q t.val g.val coefficients (columns.map CollisionProgram.encodeType)
          out i.val [] ((ConstraintMatrixSlot.rowsBytes p i t coefficients rows columns).reverse ++ accumulator)
          (List.replicate rows.length true ++ rowCount) remaining) := by
  let side := columns.map CollisionProgram.encodeType
  let joints := ProgramEncoding.encodeRecords (rows.map CollisionProgram.encodeType)
  let bytes := ConstraintMatrixSlot.rowsBytes p i t coefficients rows columns
  let nextAcc := bytes.reverse ++ accumulator
  let nextCount := List.replicate rows.length true ++ rowCount
  let a := state p r Q t.val g.val coefficients side regs i.val joints accumulator rowCount remaining
  have hp : projectState slotRegisters slotPorts a =
      ConstraintMatrixSlot.state (ConstraintMatrixSlot.context p i t anchor coefficients)
        (regs ∘ slotRegisters) joints (ProgramEncoding.encodeRecords side) accumulator rowCount :=
    project_slot p i t g anchor coefficients side regs joints accumulator rowCount remaining
  obtain ⟨sr, n, hn, ht⟩ := ConstraintMatrixSlot.program_runsIn p h2 i t anchor coefficients
    rows columns E hE (regs ∘ slotRegisters) accumulator rowCount
  let smallOut := ConstraintMatrixSlot.state (ConstraintMatrixSlot.context p i t anchor coefficients)
    sr [] (ProgramEncoding.encodeRecords side) nextAcc nextCount
  have ht' : Trace ConstraintMatrixSlot.program n
      ((projectState slotRegisters slotPorts a).withPC (some ConstraintMatrixSlot.program.entry))
      (smallOut.withPC none) := by
    rw [hp]
    exact ht
  have he := eval_call_from_state ConstraintMatrixSlot.program slotRegisters slotPorts a
    slotRegisters_injective slotPorts_injective ht'
  let out := Function.extend slotRegisters sr regs
  have hl : smallOut.stacks =
      Function.update (Function.update (Function.update
        (projectState slotRegisters slotPorts a).stacks 51 []) 50 nextAcc) 55 nextCount := by
    rw [hp]
    funext j
    fin_cases j <;> rfl
  have hb : Function.extend slotPorts (projectState slotRegisters slotPorts a).stacks a.stacks =
      a.stacks := congrArg StructuredProgram.State.stacks
        (embedState_project slotRegisters slotPorts a slotRegisters_injective slotPorts_injective)
  have hend : embedState slotRegisters slotPorts a smallOut =
      state p r Q t.val g.val coefficients side out i.val [] nextAcc nextCount remaining := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hl, ProgramLinking.extend_update slotPorts_injective,
        ProgramLinking.extend_update slotPorts_injective,
        ProgramLinking.extend_update slotPorts_injective, hb]
      funext j
      by_cases h50 : j = 50
      · subst j; simp [slotPorts]
      by_cases h51 : j = 51
      · subst j; simp [slotPorts]
      by_cases h55 : j = 55
      · subst j; simp [slotPorts]
      simp [slotPorts, a, state, h50, h51, h55]
  exact ⟨n, hn, out, hend ▸ he⟩

end SubexponentialSAT.Subexp.ConstraintMatrixProgram

end OAI.Algorithms
