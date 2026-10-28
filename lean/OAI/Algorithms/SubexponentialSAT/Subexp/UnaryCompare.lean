import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalExpectation
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A fixed bit program for exact conditional-score comparisons

The local conditional scores admit bounded natural numerators. Unary storage
is therefore already polynomial in the growing parameters. This module gives
an actual fixed finite instruction table comparing two stack lengths and
connects its measured execution to those conditional scores.
-/

namespace SubexponentialSAT.Subexp.UnaryCompare

open SubexponentialSAT.BitProgram

/-- Compare stack lengths destructively. Register 3 receives `left ≤ right`.
The four registers, two stacks, and seven labels do not depend on the data. -/
abbrev program : Program 4 2 7 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 0 2 2
    | 2 => .branch 1 3 5
    | 3 => .branch 2 0 4
    | 4 => .set 3 false 6
    | 5 => .set 3 true 6
    | _ => .halt

def pairStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys

def start (regs : Fin 4 → Bool) (xs ys : List Bool) : Cfg 4 2 7 :=
  ⟨some 0, regs, pairStacks xs ys⟩

def poppedRegs (regs : Fin 4 → Bool) (x y : Option Bool) : Fin 4 → Bool :=
  readRegs (readRegs regs 0 1 x) 0 2 y

def finish (regs : Fin 4 → Bool) (xs ys : List Bool) (answer : Bool) : Cfg 4 2 7 :=
  ⟨none, Function.update regs 3 answer, pairStacks xs ys⟩

theorem nil_left (regs : Fin 4 → Bool) (ys : List Bool) :
    Trace program 5 (start regs [] ys)
      (finish (poppedRegs regs none ys.head?) [] ys.tail true) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

theorem cons_nil (regs : Fin 4 → Bool) (x : Bool) (xs : List Bool) :
    Trace program 6 (start regs (x :: xs) [])
      (finish (poppedRegs regs (some x) none) xs [] false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

theorem cons_cons (regs : Fin 4 → Bool) (x y : Bool) (xs ys : List Bool) :
    Trace program 4 (start regs (x :: xs) (y :: ys))
      (start (poppedRegs regs (some x) (some y)) xs ys) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

/-- The cost counts actual instructions, including the halt instruction. -/
theorem runs (regs : Fin 4 → Bool) (xs ys : List Bool) :
    ∃ n ≤ 4 * min xs.length ys.length + 6, ∃ c : Cfg 4 2 7,
      Trace program n (start regs xs ys) c ∧
      c.pc = none ∧ c.regs 3 = decide (xs.length ≤ ys.length) := by
  induction xs generalizing regs ys with
  | nil =>
      refine ⟨5, by simp, finish (poppedRegs regs none ys.head?) [] ys.tail true,
        nil_left regs ys, rfl, ?_⟩
      simp [finish]
  | cons x xs ih =>
      cases ys with
      | nil =>
          refine ⟨6, by simp, finish (poppedRegs regs (some x) none) xs [] false,
            cons_nil regs x xs, rfl, ?_⟩
          simp [finish]
      | cons y ys =>
          obtain ⟨n, hn, c, ht, hpc, hout⟩ := ih (poppedRegs regs (some x) (some y)) ys
          refine ⟨4 + n, ?_, c, (cons_cons regs x y xs ys).trans ht, hpc, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa using hout

theorem runsIn (regs : Fin 4 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 4 2 7,
      RunsIn program (4 * min xs.length ys.length + 6) (start regs xs ys) c ∧
      c.pc = none ∧ c.regs 3 = decide (xs.length ≤ ys.length) := by
  obtain ⟨n, hn, c, ht, hpc, hout⟩ := runs regs xs ys
  exact ⟨c, ⟨n, hn, ht⟩, hpc, hout⟩

theorem step_length_le {c c' : Cfg 4 2 7}
    (h : step program c = some c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at h
  | some q =>
      have he : execInstr (program.code q) c = c' := by simpa [step, hpc] using h
      subst c'
      fin_cases q <;> simp [ execInstr]
      all_goals
        simp only [Function.update_apply]
        split <;> simp_all [List.length_tail]

theorem trace_length_le {c c' : Cfg 4 2 7} {n : ℕ}
    (h : Trace program n c c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  induction h with
  | refl => exact le_rfl
  | cons hs ht ih => exact ih.trans (step_length_le hs i)

/-- A unary natural is represented only by its stack length. -/
def encode (n : ℕ) : List Bool := List.replicate n false

@[simp] theorem encode_length (n : ℕ) : (encode n).length = n := by
  simp [encode]

theorem natural_runsIn (regs : Fin 4 → Bool) (m n : ℕ) :
    ∃ c : Cfg 4 2 7,
      RunsIn program (4 * min m n + 6) (start regs (encode m) (encode n)) c ∧
      c.pc = none ∧ c.regs 3 = decide (m ≤ n) := by
  simpa using runsIn regs (encode m) (encode n)

/-- The proved generic compiler supplies an actual primitive-bit-machine run
from this two-stack input boundary. -/
theorem natural_primitive_runsIn (regs : Fin 4 → Bool) (m n : ℕ) :
    ∃ c : Cfg 4 2 7,
      SubexponentialSAT.Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (4 * min m n + 6))
        (primitiveCfg program (start regs (encode m) (encode n)))
        (primitiveCfg program c) ∧
      c.pc = none ∧ c.regs 3 = decide (m ≤ n) := by
  obtain ⟨c, hr, hpc, hout⟩ := natural_runsIn regs m n
  exact ⟨c, primitive_execution program hr, hpc, hout⟩

/-- Reuse the comparison subroutine and expose its answer on the output
stack. The linker replaces the old halt with a return. -/
def outputCommand : SubexponentialSAT.StructuredCalls.Cmd 4 2 :=
  .seq (.call program) (.base (.atom (.push 0 3)))

abbrev outputProgram : Program 4 2 9 :=
  SubexponentialSAT.StructuredCalls.compiled outputCommand 0 0

def outputStart (regs : Fin 4 → Bool) (xs ys : List Bool) : Cfg 4 2 9 :=
  ⟨some outputProgram.entry, regs, pairStacks xs ys⟩

theorem output_trace (regs : Fin 4 → Bool) (xs ys : List Bool) :
    ∃ n ≤ 4 * min xs.length ys.length + 8, ∃ c : Cfg 4 2 9,
      Trace outputProgram n (outputStart regs xs ys) c ∧ c.pc = none ∧
      (c.stacks 0).head? = some (decide (xs.length ≤ ys.length)) := by
  obtain ⟨n, hn, c, ht, hp, hout⟩ := runs regs xs ys
  let a : SubexponentialSAT.StructuredProgram.State 4 2 := ⟨regs, pairStacks xs ys⟩
  let b : SubexponentialSAT.StructuredProgram.State 4 2 := ⟨c.regs, c.stacks⟩
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, SubexponentialSAT.StructuredProgram.State.withPC]
  have ht' : Trace program n (a.withPC (some program.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  let d := (SubexponentialSAT.StructuredProgram.Atom.push (0 : Fin 2) (3 : Fin 4)).eval b
  have he : SubexponentialSAT.StructuredCalls.Eval outputCommand (n + 1) a d :=
    .seq (.call _ ht') (.base (.atom _ _))
  have hr := SubexponentialSAT.StructuredCalls.compiled_halt_trace he (0 : Fin 2) 0
  refine ⟨n + 1 + 1, by omega, d.withPC none, hr, rfl, ?_⟩
  simp [d, b, SubexponentialSAT.StructuredProgram.Atom.eval,
    SubexponentialSAT.StructuredProgram.Atom.instr, SubexponentialSAT.StructuredProgram.State.ofCfg, execInstr, hout]

/-- A real primitive-machine terminal answer at the prepared two-stack input
boundary. The overhead is a constant of the one fixed output program. -/
theorem output_primitive_runsIn (regs : Fin 4 → Bool) (m n : ℕ) :
    ∃ c : (primitive outputProgram).Cfg,
      SubexponentialSAT.Computation.RunsIn (primitive outputProgram).step
        (primitiveOverhead outputProgram * (4 * min m n + 8))
        (primitiveCfg outputProgram (outputStart regs (encode m) (encode n))) c ∧
      c.state = .inl (decide (m ≤ n)) := by
  obtain ⟨time, htime, c, ht, hpc, hout⟩ := output_trace regs (encode m) (encode n)
  simp only [encode_length] at htime hout
  refine ⟨primitiveCfg outputProgram c,
    primitive_execution outputProgram ⟨time, htime, ht⟩, ?_⟩
  rw [primitive_halted outputProgram c hpc]
  change Sum.inl ((c.stacks 0).head?.getD false) = Sum.inl (decide (m ≤ n))
  rw [hout]
  rfl

section Scores

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment
open SubexponentialSAT.Subexp.LocalExpectation

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

/-- The fixed program compares the exact conditional scores. Its input size
and actual instruction count are polynomial in the growing parameters. -/
theorem conditional_score_runsIn (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining₁ remaining₂ : List (SeedIndex V E Δ))
    (hr₁ : remaining₁.Nodup) (hr₂ : remaining₂.Nodup)
    (ω₁ ω₂ : Assignment V E r Q Δ) (regs : Fin 4 → Bool) :
    ∃ c : Cfg 4 2 7,
      RunsIn program (4 * (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) + 6)
        (start regs
          (encode (pairNumerator P slots alphabet vertices remaining₁ ω₁))
          (encode (pairNumerator P slots alphabet vertices remaining₂ ω₂))) c ∧
      c.pc = none ∧ c.regs 3 = decide
        (pairEvaluator P slots alphabet vertices remaining₁ ω₁ ≤
         pairEvaluator P slots alphabet vertices remaining₂ ω₂) := by
  obtain ⟨c, hrun, hpc, hout⟩ := natural_runsIn regs
    (pairNumerator P slots alphabet vertices remaining₁ ω₁)
    (pairNumerator P slots alphabet vertices remaining₂ ω₂)
  refine ⟨c, hrun.mono ?_, hpc, ?_⟩
  · have hm := (Nat.min_le_left
        (pairNumerator P slots alphabet vertices remaining₁ ω₁)
        (pairNumerator P slots alphabet vertices remaining₂ ω₂)).trans
      (pairNumerator_le P slots alphabet haNodup haFull vertices remaining₁ hr₁ ω₁)
    omega
  · simpa only [pairEvaluator_le_iff_numerator_le P slots alphabet ha haNodup haFull
      vertices remaining₁ remaining₂ hr₁ hr₂ ω₁ ω₂] using hout

/-- Primitive-machine execution of the same exact score comparison, with a
fixed compiler overhead independent of all layout parameters. -/
theorem conditional_score_primitive_runsIn
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining₁ remaining₂ : List (SeedIndex V E Δ))
    (hr₁ : remaining₁.Nodup) (hr₂ : remaining₂.Nodup)
    (ω₁ ω₂ : Assignment V E r Q Δ) (regs : Fin 4 → Bool) :
    ∃ c : Cfg 4 2 7,
      SubexponentialSAT.Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (4 * (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) + 6))
        (primitiveCfg program (start regs
          (encode (pairNumerator P slots alphabet vertices remaining₁ ω₁))
          (encode (pairNumerator P slots alphabet vertices remaining₂ ω₂))))
        (primitiveCfg program c) ∧
      c.pc = none ∧ c.regs 3 = decide
        (pairEvaluator P slots alphabet vertices remaining₁ ω₁ ≤
         pairEvaluator P slots alphabet vertices remaining₂ ω₂) := by
  obtain ⟨c, hrun, hpc, hout⟩ := conditional_score_runsIn P slots alphabet ha
    haNodup haFull vertices remaining₁ remaining₂ hr₁ hr₂ ω₁ ω₂ regs
  exact ⟨c, primitive_execution program hrun, hpc, hout⟩

/-- The primitive output bit is the order of the exact conditional scores. -/
theorem conditional_score_output_primitive_runsIn
    (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining₁ remaining₂ : List (SeedIndex V E Δ))
    (hr₁ : remaining₁.Nodup) (hr₂ : remaining₂.Nodup)
    (ω₁ ω₂ : Assignment V E r Q Δ) (regs : Fin 4 → Bool) :
    ∃ c : (primitive outputProgram).Cfg,
      SubexponentialSAT.Computation.RunsIn (primitive outputProgram).step
        (primitiveOverhead outputProgram *
          (4 * (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) + 8))
        (primitiveCfg outputProgram (outputStart regs
          (encode (pairNumerator P slots alphabet vertices remaining₁ ω₁))
          (encode (pairNumerator P slots alphabet vertices remaining₂ ω₂)))) c ∧
      c.state = .inl (decide
        (pairEvaluator P slots alphabet vertices remaining₁ ω₁ ≤
         pairEvaluator P slots alphabet vertices remaining₂ ω₂)) := by
  obtain ⟨c, hrun, hout⟩ := output_primitive_runsIn regs
    (pairNumerator P slots alphabet vertices remaining₁ ω₁)
    (pairNumerator P slots alphabet vertices remaining₂ ω₂)
  refine ⟨c, hrun.mono ?_, ?_⟩
  · apply Nat.mul_le_mul_left
    have hm := (Nat.min_le_left
        (pairNumerator P slots alphabet vertices remaining₁ ω₁)
        (pairNumerator P slots alphabet vertices remaining₂ ω₂)).trans
      (pairNumerator_le P slots alphabet haNodup haFull vertices remaining₁ hr₁ ω₁)
    omega
  · simpa only [pairEvaluator_le_iff_numerator_le P slots alphabet ha haNodup haFull
      vertices remaining₁ remaining₂ hr₁ hr₂ ω₁ ω₂] using hout

end Scores

end SubexponentialSAT.Subexp.UnaryCompare

end OAI.Algorithms
