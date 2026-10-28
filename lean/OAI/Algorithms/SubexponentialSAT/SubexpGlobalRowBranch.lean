import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableProgram
import OAI.Algorithms.SubexponentialSAT.SubexpHornerProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual finite helpers for the global packing cases of a row. Constants
are emitted from stored source-field words, and comparisons inspect real bit
strings. Neither operation chooses a row through a semantic oracle. -/

namespace SubexponentialSAT.SubexpGlobalRowBranch

open BitProgram StructuredCalls SubexpDenseRowTableProgram

def literalPorts (source : Fin 288) : Fin 3 → Fin 288 := ![source, 284, 285]

theorem literalPorts_injective (source : Fin 288)
    (h284 : source ≠ 284) (h285 : source ≠ 285) : Function.Injective (literalPorts source) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [literalPorts]

def literalEmit (source : Fin 288) : Code :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program
    smallRegisters (literalPorts source))

def literalWord (bits : Word) : Word := false :: Encoding.frame bits

def emittedLiteral (source : Fin 288) (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 true,
    Function.update a.stacks 284 (literalWord (a.stacks source)).reverse⟩

theorem literalEmit_eval (source : Fin 288) (a : Data)
    (h284 : source ≠ 284) (h285 : source ≠ 285)
    (ha284 : a.stacks 284 = []) (ha285 : a.stacks 285 = []) :
    Eval (literalEmit source) (8 * (a.stacks source).length + 9) a (emittedLiteral source a) := by
  let before : State 3 3 :=
    ⟨SubexpHornerProgram.triple (a.regs 0) (a.regs 1) (a.regs 2),
      SubexpHornerProgram.triple (a.stacks source) [] []⟩
  let after : State 3 3 :=
    ⟨SubexpHornerProgram.triple false false true,
      SubexpHornerProgram.triple (a.stacks source) (literalWord (a.stacks source)).reverse []⟩
  have hi := literalPorts_injective source h284 h285
  have hbefore : embedState smallRegisters (literalPorts source) a before = a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hi
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i
      fin_cases i
      · rfl
      · exact ha284
      · exact ha285
    · intros; rfl
  have hafter : embedState smallRegisters (literalPorts source) a after = emittedLiteral source a := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegisters_injective hi
    · intro i
      fin_cases i <;> simp [after, smallRegisters, SubexpHornerProgram.triple, emittedLiteral]
    · intro i h
      have h0 : i ≠ 0 := fun e => h ⟨0, e.symm⟩
      have h1 : i ≠ 1 := fun e => h ⟨1, e.symm⟩
      have h2 : i ≠ 2 := fun e => h ⟨2, e.symm⟩
      simp [emittedLiteral, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [after, literalPorts, SubexpHornerProgram.triple, emittedLiteral,
        h284, ha285]
    · intro i h
      have h284i : i ≠ 284 := fun e => h ⟨1, e.symm⟩
      simp [emittedLiteral, h284i]
  have ht := SubexpHornerProgram.Literal.trace (a.stacks source) []
    (a.regs 0) (a.regs 1) (a.regs 2)
  simp only [List.append_nil] at ht
  have ht' : Trace SubexpHornerProgram.Literal.program (8 * (a.stacks source).length + 9)
      (before.withPC (some SubexpHornerProgram.Literal.program.entry))
      (after.withPC none) := ht
  have he := eval_call_lifted SubexpHornerProgram.Literal.program smallRegisters (literalPorts source)
    a smallRegisters_injective hi ht'
  change Eval (literalEmit source) _
    (embedState smallRegisters (literalPorts source) a before)
    (embedState smallRegisters (literalPorts source) a after) at he
  simpa only [hbefore, hafter] using he

def literal (source : Fin 288) : Code :=
  .seq (literalEmit source) (transfer 284 26)

def literalResult (source : Fin 288) (a : Data) (regs : Fin 25 → Bool) : Data :=
  ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks source))⟩

/-- Preserve the stored constant, generate its real postfix literal, and
restore both scratch stacks. Source131 and source132 give zero and one. -/
theorem literal_eval (source : Fin 288) (a : Data)
    (h284 : source ≠ 284) (h285 : source ≠ 285)
    (ha26 : a.stacks 26 = []) (ha284 : a.stacks 284 = []) (ha285 : a.stacks 285 = []) :
    ∃ regs, Eval (literal source) (14 * (a.stacks source).length + 18) a
      (literalResult source a regs) := by
  let b := emittedLiteral source a
  let c := transferred 284 26 b
  have h1 := literalEmit_eval source a h284 h285 ha284 ha285
  have h2 := transfer_eval 284 26 (by decide) b
  have hc : c = literalResult source a c.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi26 : i = 26
      · subst i
        simp [b, emittedLiteral, StackRoutines.transferStacks, ha26]
      by_cases hi284 : i = 284
      · subst i
        simp [b, StackRoutines.transferStacks, ha284]
      simp [b, emittedLiteral, StackRoutines.transferStacks, hi26, hi284]
  refine ⟨c.regs, ?_⟩
  have he := h1.seq h2
  change Eval (literal source) _ a c at he
  rw [hc] at he
  convert he using 1
  simp [b, emittedLiteral, literalWord, Encoding.length_frame, Nat.mul_add]
  omega

theorem literalResult_source (source : Fin 288) (a : Data) (regs : Fin 25 → Bool)
    (h26 : source ≠ 26) : (literalResult source a regs).stacks source = a.stacks source := by
  simp [literalResult, h26]

def equalityRegisters : Fin 5 → Fin 25 := Fin.castAdd 20
def equalityPorts : Fin 2 → Fin 288 := ![284, 285]

theorem equalityRegisters_injective : Function.Injective equalityRegisters := by
  exact Fin.castAdd_injective _ _

theorem equalityPorts_injective : Function.Injective equalityPorts := by decide

def equality : Code := .call (ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram
  equalityRegisters equalityPorts)

theorem equality_eval (a : Data) :
    ∃ n ≤ 9 * ((a.stacks 284).length + 1), ∃ b : Data,
      Eval equality n a b ∧ b.regs 4 = decide (a.stacks 284 = a.stacks 285) ∧
      (b.stacks 284).length ≤ (a.stacks 284).length ∧
      (b.stacks 285).length ≤ (a.stacks 285).length ∧
      (∀ i, i ≠ 284 → i ≠ 285 → b.stacks i = a.stacks i) ∧
      (∀ i : Fin 25, 5 ≤ i.val → b.regs i = a.regs i) := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded (a.regs ∘ equalityRegisters)
      (a.stacks 284) (a.stacks 285)
  let first : State 5 2 := ⟨a.regs ∘ equalityRegisters,
    ExecClauseCost.bitStacks (a.stacks 284) (a.stacks 285)⟩
  let last : State 5 2 := ⟨c.regs, c.stacks⟩
  have hfirst : projectState equalityRegisters equalityPorts a = first := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> rfl
  have hlast : last.withPC none = c := by
    cases c
    simp_all [last, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      ((projectState equalityRegisters equalityPorts a).withPC
        (some ExecClauseCost.bitEqualityProgram.entry)) (last.withPC none) := by
    rw [hfirst, hlast]
    exact ht
  let b := embedState equalityRegisters equalityPorts a last
  have he := eval_call_from_state ExecClauseCost.bitEqualityProgram equalityRegisters equalityPorts a
    equalityRegisters_injective equalityPorts_injective ht'
  refine ⟨n, hn, b, he, ?_, ?_, ?_, ?_, ?_⟩
  · change b.regs (equalityRegisters 4) = _
    rw [embedState_register _ _ _ _ equalityRegisters_injective]
    exact hout
  · change (b.stacks (equalityPorts 0)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hleft
  · change (b.stacks (equalityPorts 1)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hright
  · intro i hi hj
    apply embedState_stack_frame
    rintro ⟨j, h⟩
    fin_cases j <;> simp_all [equalityPorts]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, h⟩
    have hv := congrArg (fun k : Fin 25 => k.val) h
    have hj := j.isLt
    change j.val = i.val at hv
    omega

def compare (left right : Fin 288) : Code :=
  .seq (copy left 284) (.seq (copy right 285)
    (.seq equality (.seq (clear 284) (clear 285))))

/-- Preserving bit comparison. Both copied prefixes and any unmatched tails
are really cleared; the answer is in register4 and high control flags survive. -/
theorem compare_eval (left right : Fin 288) (a : Data)
    (hl284 : left ≠ 284) (hl270 : left ≠ 270)
    (hr284 : right ≠ 284) (hr285 : right ≠ 285) (hr270 : right ≠ 270)
    (ha284 : a.stacks 284 = []) (ha285 : a.stacks 285 = []) (ha270 : a.stacks 270 = []) :
    ∃ n ≤ 18 * (a.stacks left).length + 9 * (a.stacks right).length + 25, ∃ regs,
      Eval (compare left right) n a ⟨regs, a.stacks⟩ ∧
      regs 4 = decide (a.stacks left = a.stacks right) ∧
      (∀ i : Fin 25, 5 ≤ i.val → regs i = a.regs i) := by
  let b := copied left 284 a
  let c := copied right 285 b
  have h1 := copy_eval left 284 hl284 hl270 (by decide) a ha270
  have hb270 : b.stacks 270 = [] := by
    simp [b, copied, StackRoutines.copyStacks, ha270]
  have h2 := copy_eval right 285 hr285 hr270 (by decide) b hb270
  have hc284 : c.stacks 284 = a.stacks left := by
    simp [c, b, copied, StackRoutines.copyStacks, ha284]
  have hc285 : c.stacks 285 = a.stacks right := by
    simp [c, b, copied, StackRoutines.copyStacks, hr284, ha285]
  obtain ⟨n, hn, d, hd, hanswer, hleft, hright, hframe, hregs⟩ := equality_eval c
  let e := cleared 284 d
  let f := cleared 285 e
  have h3 := clear_eval 284 d
  have h4 := clear_eval 285 e
  have hf : f = (⟨f.regs, a.stacks⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 284
      · subst i; simp [e, cleared, StackRoutines.clearStacks, ha284]
      by_cases hj : i = 285
      · subst i; simp [StackRoutines.clearStacks, ha285]
      have hdi := hframe i hi hj
      simpa [f, e, cleared, StackRoutines.clearStacks, c, b, copied,
        StackRoutines.copyStacks, hi, hj] using hdi
  have run := h1.seq (h2.seq (hd.seq (h3.seq h4)))
  refine ⟨(7 * (a.stacks left).length + 5) +
    ((7 * (b.stacks right).length + 5) +
      (n + ((2 * (d.stacks 284).length + 3) + (2 * (e.stacks 285).length + 3)))),
    ?_, f.regs, ?_, ?_, ?_⟩
  · rw [hc284] at hn hleft
    rw [hc285] at hright
    have hbr : b.stacks right = a.stacks right := by
      simp [b, copied, StackRoutines.copyStacks, hr284]
    have he285 : e.stacks 285 = d.stacks 285 := by
      simp [e, cleared, StackRoutines.clearStacks]
    rw [hbr, he285]
    omega
  · change Eval (compare left right) _ a f at run
    rw [hf] at run
    exact run
  · simpa [f, e, cleared, readRegs, hc284, hc285] using hanswer
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hh := hregs i hi
    simpa [f, e, cleared, c, b, copied, readRegs, hi0, hi1] using hh

end SubexponentialSAT.SubexpGlobalRowBranch

end OAI.Algorithms
