import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramSelect
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! One concrete greedy round copies the saved family, evaluates every row,
selects a binary minimum, and prepends the winner to the current matrix. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

variable {r s : ℕ}

structure RoundPorts (r s : ℕ) where
  core : Ports r s
  rows : Fin s
  family : Fin s
  rows_outside : ∀ i, core.stack i ≠ rows
  family_outside : ∀ i, core.stack i ≠ family

def wordPorts (p : RoundPorts r s) : RecordPrograms.Ports r s where
  tag := p.core.register 0
  present := p.core.register 1
  found := p.core.register 7
  source := p.core.stack 2
  payload := p.rows
  tag_ne_present := fun h => by have := p.core.register_injective h; contradiction
  found_ne_tag := fun h => by have := p.core.register_injective h; contradiction
  found_ne_present := fun h => by have := p.core.register_injective h; contradiction
  source_ne_payload := p.rows_outside 2

abbrev appendWinner (p : RoundPorts r s) : Cmd r s :=
  .seq (TupleProgram.pushConst p.rows (p.core.register 0) false)
    (.seq (TupleProgram.escape (wordPorts p))
      (.seq (TupleProgram.pushConst p.rows (p.core.register 0) true)
        (.call (StackRoutines.clearProgram (p.core.stack 3)
          (p.core.register 0) (p.core.register 1)))))

def afterAppend (p : RoundPorts r s) (a : State r s) : State r s :=
  let b := TupleProgram.pushedState p.rows (p.core.register 0) false a
  let c := TupleProgram.escapedState (wordPorts p) b
  let d := TupleProgram.pushedState p.rows (p.core.register 0) true c
  ⟨readRegs d.regs (p.core.register 0) (p.core.register 1) none,
    StackRoutines.clearStacks (p.core.stack 3) d.stacks⟩

theorem appendWinner_eval (p : RoundPorts r s) (a : State r s) :
    Eval (appendWinner p)
      (5 * (a.stacks (p.core.stack 2)).length + 2 * (a.stacks (p.core.stack 3)).length + 10)
      a (afterAppend p a) := by
  let b := TupleProgram.pushedState p.rows (p.core.register 0) false a
  let c := TupleProgram.escapedState (wordPorts p) b
  let d := TupleProgram.pushedState p.rows (p.core.register 0) true c
  have h23 : p.core.stack 3 ≠ p.core.stack 2 := fun h => by
    have := p.core.stack_injective h; contradiction
  have h1 := TupleProgram.pushConst_eval p.rows (p.core.register 0) false a
  have h2 := TupleProgram.escape_eval_state (wordPorts p) b
  have h3 := TupleProgram.pushConst_eval p.rows (p.core.register 0) true c
  have h4 := TupleProgram.clear_eval (p.core.stack 3) (p.core.register 0) (p.core.register 1) d
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    simp [ afterAppend, b, c, d, wordPorts, p.rows_outside, h23] ; omega

theorem afterAppend_rows (p : RoundPorts r s) (a : State r s) :
    (afterAppend p a).stacks p.rows =
      true :: (Encoding.frame (a.stacks (p.core.stack 2)).reverse ++ a.stacks p.rows) := by
  simp [afterAppend, StackRoutines.clearStacks, wordPorts, Ne.symm (p.rows_outside 3),
    p.rows_outside, TupleProgram.frame_eq_escaped,
    List.append_assoc]

theorem afterAppend_payload (p : RoundPorts r s) (a : State r s) :
    (afterAppend p a).stacks (p.core.stack 2) = [] := by
  have h23 : p.core.stack 2 ≠ p.core.stack 3 := fun h => by
    have := p.core.stack_injective h; contradiction
  simp [afterAppend, StackRoutines.clearStacks, wordPorts, p.rows_outside, h23]

@[simp] theorem afterAppend_score (p : RoundPorts r s) (a : State r s) :
    (afterAppend p a).stacks (p.core.stack 3) = [] := by
  simp [afterAppend, StackRoutines.clearStacks]

theorem afterAppend_stack_frame (p : RoundPorts r s) (a : State r s) (i : Fin s)
    (hr : i ≠ p.rows) (h2 : i ≠ p.core.stack 2) (h3 : i ≠ p.core.stack 3) :
    (afterAppend p a).stacks i = a.stacks i := by
  simp [afterAppend, StackRoutines.clearStacks, wordPorts, hr, h2, h3]

theorem afterAppend_core_empty (p : RoundPorts r s) (frame : State r s)
    (regs : Fin 8 → Bool) (best : Entry) :
    ∀ i, (afterAppend p (state p.core frame regs BinaryArgmin.empty best [])).stacks
      (p.core.stack i) = [] := by
  intro i
  by_cases h2 : i = 2
  · subst i; exact afterAppend_payload _ _
  by_cases h3 : i = 3
  · subst i; exact afterAppend_score _ _
  rw [afterAppend_stack_frame p _ _ (p.rows_outside i)
    (fun h => h2 (p.core.stack_injective h)) (fun h => h3 (p.core.stack_injective h))]
  rw [state_stack]
  fin_cases i <;> simp_all [BinaryArgmin.store, BinaryArgmin.empty]

abbrev copyFamily (p : RoundPorts r s) : Cmd r s :=
  .call (StackRoutines.copyProgram p.family (p.core.stack 8) (p.core.stack 7)
    (p.core.register 0) (p.core.register 1))

def afterCopyFamily (p : RoundPorts r s) (a : State r s) : State r s :=
  ⟨readRegs a.regs (p.core.register 0) (p.core.register 1) none,
    StackRoutines.copyStacks p.family (p.core.stack 8) a.stacks⟩

theorem copyFamily_eval (p : RoundPorts r s) (a : State r s)
    (ht : a.stacks (p.core.stack 7) = []) :
    Eval (copyFamily p) (7 * (a.stacks p.family).length + 5) a (afterCopyFamily p a) := by
  exact TupleProgram.copy_eval p.family (p.core.stack 8) (p.core.stack 7)
    (p.core.register 0) (p.core.register 1) (Ne.symm (p.family_outside 8))
    (Ne.symm (p.family_outside 7))
    (fun h => by have := p.core.stack_injective h; contradiction)
    (fun h => by have := p.core.register_injective h; contradiction) a ht

/-- Genuine fixed code: no input-dependent unrolling and no semantic atom. -/
abbrev round (p : RoundPorts r s) (mass : Cmd r s) : Cmd r s :=
  .seq (copyFamily p) (.seq (select p.core mass) (appendWinner p))

def roundBudget (B C cost familyBits count : ℕ) : ℕ :=
  7 * familyBits + 5 + selectBudget B C cost count + 5 * C + 2 * B + 10

/-- The only unimplemented computation in this composition is exactly the
explicitly supplied and traced `mass` command. `shape` is an ABI equality
about the copied queue, not a computation or an oracle assumption. -/
theorem round_eval (p : RoundPorts r s) (mass : Cmd r s) (a frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p.core frame score valid B C cost)
    (seed : List Bool) (rest : List (List Bool)) (regs : Fin 8 → Bool)
    (htmp : a.stacks (p.core.stack 7) = [])
    (shape : afterCopyFamily p a =
      state p.core frame regs BinaryArgmin.empty BinaryArgmin.empty
        (candidateEncoding (seed :: rest)))
    (hp : ∀ bits ∈ seed :: rest, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ roundBudget B C cost (a.stacks p.family).length (rest.length + 1),
      ∃ regs',
        Eval (round p mass) n a
          (afterAppend p (state p.core frame regs' BinaryArgmin.empty
            (HashSelect.best BinaryArgmin.value (scored score seed)
              (rest.map (scored score))) [])) := by
  have hc := copyFamily_eval p a htmp
  rw [shape] at hc
  obtain ⟨n, hn, regs', _, hs⟩ := select_cons p.core mass frame score valid B C cost
    hmass seed rest regs hp
  let best := HashSelect.best BinaryArgmin.value (scored score seed) (rest.map (scored score))
  have hfit : BinaryArgmin.Fits B C best := by
    dsimp only [best]
    have hm := HashSelect.best_mem BinaryArgmin.value (scored score seed) (rest.map (scored score))
    rcases List.mem_cons.mp hm with he | he
    · rw [he]
      exact ⟨(hp seed (by simp)).2.2, (hp seed (by simp)).2.1⟩
    · obtain ⟨bits, hb, he⟩ := List.mem_map.mp he
      rw [← he]
      exact ⟨(hp bits (by simp [hb])).2.2, (hp bits (by simp [hb])).2.1⟩
  let b := state p.core frame regs' BinaryArgmin.empty best []
  have ha := appendWinner_eval p b
  have hb2 : b.stacks (p.core.stack 2) = best.payload := by simp [b, BinaryArgmin.store]
  have hb3 : b.stacks (p.core.stack 3) = best.score := by simp [b, BinaryArgmin.store]
  refine ⟨(7 * (a.stacks p.family).length + 5) +
    (n + (5 * best.payload.length + 2 * best.score.length + 10)), ?_, regs', ?_⟩
  · unfold roundBudget
    rcases hfit with ⟨hscore, hpayload⟩
    omega
  · rw [hb2, hb3] at ha
    exact Eval.seq hc (Eval.seq hs ha)

/-- Characterization of the work-bank ABI inside an arbitrary outer state. -/
theorem state_eq_self (p : Ports r s) (a : State r s) (next best : Entry)
    (queue : List Bool) (hs : ∀ i, a.stacks (p.stack i) = BinaryArgmin.store next best queue i) :
    state p a (fun i => a.regs (p.register i)) next best queue = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hi : ∃ j, p.register j = i
    · obtain ⟨j, rfl⟩ := hi
      exact state_register p a _ next best queue j
    · exact embedState_register_frame p.register p.stack a
        (BinaryArgmin.data (fun i => a.regs (p.register i)) next best queue) i hi
  · funext i
    by_cases hi : ∃ j, p.stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (state_stack p a _ next best queue j).trans (hs j).symm
    · exact embedState_stack_frame p.register p.stack a
        (BinaryArgmin.data (fun i => a.regs (p.register i)) next best queue) i hi

theorem state_stack_outside (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin s)
    (hi : ∀ j, p.stack j ≠ i) :
    (state p frame regs next best queue).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  exact hi j hj

theorem state_register_outside (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin r)
    (hi : ∀ j, p.register j ≠ i) :
    (state p frame regs next best queue).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  exact hi j hj

/-- The queue-copy shape obligation follows from ordinary empty work banks. -/
theorem copied_shape (p : RoundPorts r s) (a : State r s) (payloads : List (List Bool))
    (he : ∀ i, a.stacks (p.core.stack i) = [])
    (hf : a.stacks p.family = candidateEncoding payloads) :
    afterCopyFamily p a = state p.core (afterCopyFamily p a)
      (fun i => (afterCopyFamily p a).regs (p.core.register i))
      BinaryArgmin.empty BinaryArgmin.empty (candidateEncoding payloads) := by
  symm
  apply state_eq_self
  intro i
  fin_cases i <;>
    simp [afterCopyFamily, StackRoutines.copyStacks, p.core.stack_injective.eq_iff,
      he, hf, BinaryArgmin.store, BinaryArgmin.empty]

theorem afterAppend_register_frame (p : RoundPorts r s) (a : State r s) (i : Fin r)
    (h0 : i ≠ p.core.register 0) (h1 : i ≠ p.core.register 1) :
    (afterAppend p a).regs i = a.regs i := by
  simp [afterAppend,
    wordPorts, readRegs, h0, h1]

/-- Ready-to-run round with no abstract ABI equality assumption. -/
theorem round_eval_ready (p : RoundPorts r s) (mass : Cmd r s) (a : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p.core (afterCopyFamily p a) score valid B C cost)
    (seed : List Bool) (rest : List (List Bool))
    (he : ∀ i, a.stacks (p.core.stack i) = [])
    (hf : a.stacks p.family = candidateEncoding (seed :: rest))
    (hp : ∀ bits ∈ seed :: rest, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ roundBudget B C cost (a.stacks p.family).length (rest.length + 1),
      ∃ b, Eval (round p mass) n a b ∧
        (∀ i, b.stacks (p.core.stack i) = []) ∧
        b.stacks p.rows = true ::
          (Encoding.frame (HashSelect.best BinaryArgmin.value (scored score seed)
            (rest.map (scored score))).payload.reverse ++ a.stacks p.rows) ∧
        (∀ i, i ≠ p.rows → (∀ j, p.core.stack j ≠ i) → b.stacks i = a.stacks i) ∧
        (∀ i, (∀ j, p.core.register j ≠ i) → b.regs i = a.regs i) := by
  obtain ⟨n, hn, regs', ht⟩ := round_eval p mass a (afterCopyFamily p a)
    score valid B C cost hmass seed rest _ (he 7) (copied_shape p a _ he hf) hp
  refine ⟨n, hn, _, ht, afterAppend_core_empty _ _ _ _, ?_, ?_, ?_⟩
  · rw [afterAppend_rows, state_stack, state_stack_outside _ _ _ _ _ _ _ p.rows_outside]
    simp [BinaryArgmin.store, afterCopyFamily, StackRoutines.copyStacks,
      Ne.symm (p.rows_outside 8)]
  · intro i hi hout
    rw [afterAppend_stack_frame _ _ _ hi (Ne.symm (hout 2)) (Ne.symm (hout 3)),
      state_stack_outside _ _ _ _ _ _ _ hout]
    simp [afterCopyFamily, StackRoutines.copyStacks, Ne.symm (hout 8)]
  · intro i hout
    rw [afterAppend_register_frame _ _ _ (Ne.symm (hout 0)) (Ne.symm (hout 1)),
      state_register_outside _ _ _ _ _ _ _ hout]
    simp [afterCopyFamily, readRegs, Ne.symm (hout 0), Ne.symm (hout 1)]

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
