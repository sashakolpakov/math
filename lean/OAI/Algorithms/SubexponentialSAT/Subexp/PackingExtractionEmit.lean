import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionState
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingEntryEmitter

namespace OAI.Algorithms

/-! Lift the actual covered-entry emitter into the extraction controller. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def emitPorts : Fin 10 → Fin 19 := ![3, 1, 10, 11, 12, 13, 14, 9, 17, 18]

theorem emitPorts_injective : Function.Injective emitPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitPorts]

abbrev emitCall : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram PackingEntryEmitter.program id emitPorts)

def emitted (c : Context) (key vertex : List Bool) : Context :=
  { c with
    address := true :: c.address
    storage := PackingEntryEmitter.storageOutput vertex c.storage
    metadata := PackingEntryEmitter.metadataOutput vertex key c.block c.metadata
    addresses := PackingEntryEmitter.addressOutput vertex c.address c.addresses }

theorem emitCall_eval (c : Context) (key vertex : List Bool) (regs : Fin 8 → Bool) :
    ∃ rf, Eval emitCall (PackingEntryEmitter.commandCost vertex key c.block c.address + 1)
      (state regs c [] key [] vertex [] [] [] []) (ready rf (emitted c key vertex)) := by
  obtain ⟨rf, ht⟩ := PackingEntryEmitter.program_trace vertex key c.block c.address
    c.storage c.metadata c.addresses regs
  let a := state regs c [] key [] vertex [] [] [] []
  have hin : embedState id emitPorts a
      (PackingEntryEmitter.state regs vertex key c.block c.address c.storage c.metadata c.addresses) =
      a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState id emitPorts a
      (PackingEntryEmitter.state rf [] [] c.block (true :: c.address)
        (PackingEntryEmitter.storageOutput vertex c.storage)
        (PackingEntryEmitter.metadataOutput vertex key c.block c.metadata)
        (PackingEntryEmitter.addressOutput vertex c.address c.addresses)) =
      ready rf (emitted c key vertex) := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> rfl
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      fin_cases j <;> simp_all [a, ready, state, emitted, emitPorts]
      all_goals
        first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
          exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
          exact False.elim (hj 4 rfl) | exact False.elim (hj 5 rfl) |
          exact False.elim (hj 6 rfl)
  have he := eval_call_lifted PackingEntryEmitter.program id emitPorts a
    Function.injective_id emitPorts_injective ht
  rw [hin, hout] at he
  exact ⟨rf, he⟩

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
