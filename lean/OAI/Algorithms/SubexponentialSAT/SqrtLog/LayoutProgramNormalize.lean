import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Runtime-width normalization for signed-component matrix words. This uses
only the existing padding, clear and transfer bit programs. In particular,
normalizing a component never invokes modular integer arithmetic. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularArithmetic SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularRingPrograms

variable {s : ℕ}

/-- Local normalization ports: input/output 0, consumed unary width 7;
port 5 is preserved data. Ports 1,2,3,4,6 are empty work stacks. -/
abbrev normalizeAt (ports : Fin 8 ↪ Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram normalizeProgram id ports)

def normalizeReady (ports : Fin 8 ↪ Fin s) (d : State 8 s) : Prop :=
  ∀ i : Fin 8, i ≠ 0 → i ≠ 5 → i ≠ 7 → d.stacks (ports i) = []

def normalizedStacks (ports : Fin 8 ↪ Fin s) (d : State 8 s) : Stacks (Fin s) :=
  Function.update (Function.update d.stacks (ports 7) []) (ports 0)
    (padTo (d.stacks (ports 7)) (d.stacks (ports 0)))

private theorem normalize_embed_input (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) :
    embedState id ports d
      ⟨d.regs, normalizationState (d.stacks (ports 0)) (d.stacks (ports 7)) []
        (d.stacks (ports 5))⟩ = d := by
  apply embedState_eq_of_ports id ports d d _ Function.injective_id ports.injective
  · intro i; rfl
  · intro j hj; exact (hj ⟨j,rfl⟩).elim
  · intro i
    fin_cases i <;> simp [normalizationState] <;>
      try exact hd _ (by decide) (by decide) (by decide)
  · intro j hj; rfl

private theorem normalize_embed_output (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) (rf : Fin 8 → Bool) :
    embedState id ports d
      ⟨rf, normalizationState (padTo (d.stacks (ports 7)) (d.stacks (ports 0))) [] []
        (d.stacks (ports 5))⟩ = ⟨rf, normalizedStacks ports d⟩ := by
  apply embedState_eq_of_ports id ports d _ _ Function.injective_id ports.injective
  · intro i; rfl
  · intro j hj; exact (hj ⟨j,rfl⟩).elim
  · intro i
    have he (a b : Fin 8) : ports a = ports b ↔ a = b := ports.injective.eq_iff
    fin_cases i <;> simp [normalizedStacks, normalizationState, he] <;>
      try exact hd _ (by decide) (by decide) (by decide)
  · intro j hj
    have h0 : j ≠ ports 0 := fun h => hj ⟨0,h.symm⟩
    have h7 : j ≠ ports 7 := fun h => hj ⟨7,h.symm⟩
    simp [normalizedStacks, h0, h7]

/-- Even a long input with redundant zero bits is normalized by an actual
finite program. Both its source length and its requested width are paid. -/
theorem normalizeAt_eval (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) :
    ∃ n ≤ 7 * (d.stacks (ports 7)).length + 2 * (d.stacks (ports 0)).length + 9,
    ∃ rf, Eval (normalizeAt ports) n d ⟨rf, normalizedStacks ports d⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := normalize_correct d.regs
    (d.stacks (ports 0)) (d.stacks (ports 7)) (d.stacks (ports 5))
  have h := eval_call_lifted normalizeProgram id ports d
    Function.injective_id ports.injective
    (a := ⟨d.regs, normalizationState (d.stacks (ports 0)) (d.stacks (ports 7)) [] (d.stacks (ports 5))⟩)
    (b := ⟨rf, normalizationState (padTo (d.stacks (ports 7)) (d.stacks (ports 0))) [] [] (d.stacks (ports 5))⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [normalizeAt, normalize_embed_input ports d hd,
    normalize_embed_output ports d hd rf] using h

@[simp] theorem normalized_length (ports : Fin 8 ↪ Fin s) (d : State 8 s) :
    ((normalizedStacks ports d) (ports 0)).length = (d.stacks (ports 7)).length := by
  simp [normalizedStacks, padTo_length]

theorem normalized_value (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (h : SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0)) <
      2 ^ (d.stacks (ports 7)).length) :
    SubexponentialSAT.BinaryArithmetic.toNat ((normalizedStacks ports d) (ports 0)) =
      SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0)) := by
  simp only [normalizedStacks, Function.update_self]
  exact padTo_value_of_lt _ _ h

theorem normalized_frame (ports : Fin 8 ↪ Fin s) (d : State 8 s) (j : Fin s)
    (h0 : j ≠ ports 0) (h7 : j ≠ ports 7) :
    normalizedStacks ports d j = d.stacks j := by
  simp [normalizedStacks, h0, h7]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
