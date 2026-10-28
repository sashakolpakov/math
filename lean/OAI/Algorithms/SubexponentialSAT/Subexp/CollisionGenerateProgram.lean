import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryTally

namespace OAI.Algorithms

/-!
# Generating and evaluating collision tuples with fixed control

The alphabet and unary tuple depth are input data. The generator and collision
stream are linked through actual stack ports. The current word table and the
two selected read plans remain runtime inputs and are preserved.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateProgram

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 10 20

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def generatorPorts : Fin 9 → Fin 20 := ![16, 19, 2, 4, 5, 6, 7, 8, 17]

theorem generatorPorts_injective : Function.Injective generatorPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [generatorPorts]

abbrev generator : Cmd 10 20 :=
  .call (ProgramLinking.liftProgram TupleProgram.generateProgram id generatorPorts)

def storedState (regs : Fin 10 → Bool) (current width : List Bool) (left right : List ℕ)
    (alphabet depth tuples work stream : List Bool) : Data :=
  ⟨regs, fun j => if j = 3 then width else if j = 13 then current
    else if j = 14 then CollisionStreamProgram.planBytes left
    else if j = 15 then CollisionStreamProgram.planBytes right
    else if j = 19 then alphabet else if j = 17 then depth else if j = 16 then tuples
    else if j = 6 then work else if j = 11 then stream else []⟩

def inputState (current width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool) : Data :=
  storedState (fun _ => false) current width left right
    (ProgramEncoding.encodeRecords alphabet) depth [] [] stream

theorem generator_eval (current width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool) :
    ∃ n ≤ TupleProgram.powerCost alphabet depth.length [[]] + 9,
      ∃ regs : Fin 10 → Bool, Eval generator n
        (inputState current width left right alphabet depth stream)
        (storedState regs current width left right (ProgramEncoding.encodeRecords alphabet) []
          (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]]))
          [false] stream) := by
  let d := inputState current width left right alphabet depth stream
  let a : StructuredProgram.State 10 9 := ⟨d.regs, d.stacks ∘ generatorPorts⟩
  have ha : TupleProgram.outerInvariant alphabet depth false a := by
    simp [a, d, inputState, storedState, generatorPorts, TupleProgram.outerInvariant]
  obtain ⟨b, hb, n, hn, ht⟩ := TupleProgram.generateProgram_runsIn alphabet depth false a ha
    (by simp [a, d, inputState, storedState, generatorPorts])
    (by simp [a, d, inputState, storedState, generatorPorts])
    (by simp [a, d, inputState, storedState, generatorPorts])
  have hin : embedState id generatorPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id generatorPorts_injective
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  rcases hb with ⟨⟨hb1, hb3, hb4, hb6, hb7, hb8, _⟩, hb0, hb2, hb5⟩
  have hout : embedState id generatorPorts d b =
      storedState b.regs current width left right (ProgramEncoding.encodeRecords alphabet) []
        (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]]))
        [false] stream := by
    apply embedState_eq _ _ Function.injective_id generatorPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [storedState, generatorPorts, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h16 : j ≠ 16 := fun h => hj ⟨0, by simpa [generatorPorts] using h.symm⟩
      have h17 : j ≠ 17 := fun h => hj ⟨8, by simpa [generatorPorts] using h.symm⟩
      have h6 : j ≠ 6 := fun h => hj ⟨5, by simpa [generatorPorts] using h.symm⟩
      simp [d, inputState, storedState, h16, h17, h6]
  have he := eval_call_lifted TupleProgram.generateProgram id generatorPorts d
    Function.injective_id generatorPorts_injective ht
  exact ⟨n, hn, b.regs, by simpa only [hin, hout, generator] using he⟩

def resetList : List (Fin 10) → StructuredProgram.Cmd 10 20
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

def resetValues (indices : List (Fin 10)) (regs : Fin 10 → Bool) : Fin 10 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetValues_apply (indices : List (Fin 10)) (regs : Fin 10 → Bool) (i : Fin 10) :
    resetValues indices regs i = if i ∈ indices then false else regs i := by
  induction indices generalizing regs with
  | nil => simp [resetValues]
  | cons j rest ih =>
    change resetValues rest (Function.update regs j false) i = _
    rw [ih]
    by_cases hi : i = j <;> by_cases hr : i ∈ rest <;>
      simp_all []

theorem resetList_eval (indices : List (Fin 10)) (d : Data) :
    StructuredProgram.Eval (resetList indices) indices.length d
      ⟨resetValues indices d.regs, d.stacks⟩ := by
  induction indices generalizing d with
  | nil => exact .skip d
  | cons i rest ih =>
    have h := (StructuredProgram.Eval.atom (.set i false) d).seq
      (ih ((StructuredProgram.Atom.set i false).eval d))
    simpa [resetList, resetValues, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC, execInstr, Nat.add_comm] using h

abbrev resetCommand : Cmd 10 20 := .base (resetList (List.finRange 10))

theorem reset_eval (d : Data) :
    Eval resetCommand 10 d ⟨fun _ => false, d.stacks⟩ := by
  have he := resetList_eval (List.finRange 10) d
  have hr : resetValues (List.finRange 10) d.regs = fun _ => false := by
    funext i
    simp [resetValues_apply]
  rw [hr] at he
  simpa [resetCommand] using Eval.base he

abbrev clearWork : Cmd 10 20 := .call (clearProgram 6 0 1)

theorem clearWork_eval (regs : Fin 10 → Bool) (current width : List Bool) (left right : List ℕ)
    (alphabet tuples stream : List Bool) :
    Eval clearWork 5
      (storedState regs current width left right alphabet [] tuples [false] stream)
      (storedState (readRegs regs 0 1 none) current width left right alphabet [] tuples [] stream) := by
  let d := storedState regs current width left right alphabet [] tuples [false] stream
  have h := halt_after_trace _ (clearProgram_trace (6 : Fin 20) (0 : Fin 10) 1 d.regs d.stacks)
    2 rfl rfl
  have hs : clearStacks (6 : Fin 20) d.stacks =
      (storedState (readRegs regs 0 1 none) current width left right alphabet [] tuples [] stream).stacks := by
    funext j
    by_cases h6 : j = 6
    · subst j; simp [d, storedState, clearStacks]
    · simp [d, storedState, clearStacks, h6]
  simp only [clearResult] at h
  rw [hs] at h
  apply Eval.call
  simpa [d, clearWork, clearProgram, storedState,
    StructuredProgram.State.withPC] using h

def streamRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def streamPorts : Fin 18 → Fin 20 := Fin.castAdd 2

theorem streamRegs_injective : Function.Injective streamRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)

theorem streamPorts_injective : Function.Injective streamPorts := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 20 => k.val) h)

abbrev streamCommand : Cmd 10 20 :=
  .call (ProgramLinking.liftProgram CollisionTupleProgram.program streamRegs streamPorts)

def outputState (current width : List Bool) (left right : List ℕ)
    (alphabet stream : List Bool) : Data :=
  storedState (fun j => decide (j = 6)) current width left right alphabet [] [] [] stream

theorem stream_eval (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List Bool) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, CollisionTupleProgram.validPayload current width.length left right bits) :
    ∃ n ≤ CollisionTupleProgram.sourceBudget current.flatten width.length left right tuples,
      Eval streamCommand n
        (storedState (fun _ => false) current.flatten width left right alphabet []
          (ProgramEncoding.encodeRecords tuples) [] stream)
        (outputState current.flatten width left right alphabet
          (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream)) := by
  let d := storedState (fun _ => false) current.flatten width left right alphabet []
    (ProgramEncoding.encodeRecords tuples) [] stream
  obtain ⟨n, hn, ht⟩ := CollisionTupleProgram.program_run current width left right tuples stream hv
  have hin : embedState streamRegs streamPorts d
      (CollisionTupleProgram.inputState current.flatten width left right tuples stream) = d := by
    apply embedState_eq _ _ streamRegs_injective streamPorts_injective
    · intro i; fin_cases i <;> simp [d, storedState, streamRegs, CollisionTupleProgram.inputState,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state, RecordPrograms.state,
        CollisionTupleProgram.ports]
    · intro i; fin_cases i <;> simp [d, storedState, streamPorts, CollisionTupleProgram.inputState,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state, RecordPrograms.state,
        CollisionTupleProgram.ports]
    · intros; rfl
    · intros; rfl
  have hout : embedState streamRegs streamPorts d
      (CollisionTupleProgram.baseState current.flatten width left right
        (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream)) =
      outputState current.flatten width left right alphabet
        (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream) := by
    apply embedState_eq _ _ streamRegs_injective streamPorts_injective
    · intro i; fin_cases i <;> simp [outputState, storedState, streamRegs,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state]
    · intro i; fin_cases i <;> simp [outputState, storedState, streamPorts,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state]
    · intro j hj
      have h6 : j ≠ 6 := fun h => hj ⟨6, by simpa [streamRegs] using h.symm⟩
      simp [outputState, d, storedState, h6]
    · intro j hj
      have h16 : j ≠ 16 := fun h => hj ⟨16, by simpa [streamPorts] using h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, by simpa [streamPorts] using h.symm⟩
      simp [outputState, d, storedState, h16, h11]
  have he := eval_call_lifted CollisionTupleProgram.program streamRegs streamPorts d
    streamRegs_injective streamPorts_injective ht
  exact ⟨n, hn, by simpa only [hin, hout, streamCommand] using he⟩

abbrev command : Cmd 10 20 :=
  .seq generator (.seq clearWork (.seq resetCommand streamCommand))

abbrev program : Program 10 20 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 19 11

def sourceBudget (current : List Bool) (width : ℕ) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth : ℕ) : ℕ :=
  TupleProgram.powerCost alphabet depth [[]] +
    CollisionTupleProgram.sourceBudget current width left right
      (TupleProgram.powerRows alphabet depth [[]]) + 25

def TupleSchema (alphabet : List (List Bool)) (count : ℕ) (bits : List Bool) : Prop :=
  ∃ rows : List (List Bool), rows.length = count ∧ rows.flatten = bits ∧
    ∀ row ∈ rows, row ∈ alphabet

theorem cartesian_schema (alphabet rows : List (List Bool)) (count : ℕ)
    (hrows : ∀ bits ∈ rows, TupleSchema alphabet count bits) :
    ∀ bits ∈ TupleProgram.cartesianOutput rows alphabet, TupleSchema alphabet (count + 1) bits := by
  intro bits hbits
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap, List.mem_map] at hbits
  obtain ⟨pre, hp, word, hw, rfl⟩ := hbits
  obtain ⟨items, hn, hf, hi⟩ := hrows pre hp
  refine ⟨items ++ [word], by simp [hn], by simp [hf], ?_⟩
  intro item hitem
  simp only [List.mem_append, List.mem_singleton] at hitem
  rcases hitem with hitem | rfl
  · exact hi item hitem
  · exact hw

theorem power_schema (alphabet rows : List (List Bool)) (count depth : ℕ)
    (hrows : ∀ bits ∈ rows, TupleSchema alphabet count bits) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth rows,
      TupleSchema alphabet (count + depth) bits := by
  induction depth generalizing rows count with
  | zero => simpa [TupleProgram.powerRows] using hrows
  | succ depth ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (count + 1)
      (cartesian_schema alphabet rows count hrows)
    simpa [TupleProgram.powerRows, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Every emitted tuple consists of exactly depth original alphabet words,
even when distinct word tuples have identical concatenated payloads. -/
theorem generated_schema (alphabet : List (List Bool)) (depth : ℕ) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth [[]], TupleSchema alphabet depth bits := by
  have h := power_schema alphabet [[]] 0 depth (by
    intro bits hbits
    simp only [List.mem_singleton] at hbits
    subst bits
    exact ⟨[], rfl, rfl, by simp⟩)
  simpa using h

theorem generated_validPayload (current alphabet : List (List Bool)) (width depth : ℕ)
    (left right : List ℕ) (hc : ∀ row ∈ current, row.length = width)
    (ha : ∀ row ∈ alphabet, row.length = width)
    (hl : ∀ i ∈ left, i < current.length + depth)
    (hr : ∀ i ∈ right, i < current.length + depth) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth [[]],
      CollisionTupleProgram.validPayload current width left right bits := by
  intro bits hbits
  obtain ⟨rows, hn, hf, hm⟩ := generated_schema alphabet depth bits hbits
  refine ⟨rows, hf, ?_, ?_, ?_⟩
  · intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact hc row hrow
    · exact ha row (hm row hrow)
  · simpa [hn] using hl
  · simpa [hn] using hr

theorem program_run (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool)
    (hv : ∀ bits ∈ TupleProgram.powerRows alphabet depth.length [[]],
      CollisionTupleProgram.validPayload current width.length left right bits) :
    RunsIn program (sourceBudget current.flatten width.length left right alphabet depth.length)
      ((inputState current.flatten width left right alphabet depth stream).withPC (some program.entry))
      ((outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)).withPC none) := by
  obtain ⟨n, hn, regs, hg⟩ := generator_eval current.flatten width left right alphabet depth stream
  have hc := clearWork_eval regs current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]])) stream
  have hr := reset_eval (storedState (readRegs regs 0 1 none) current.flatten width left right
    (ProgramEncoding.encodeRecords alphabet) []
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]])) [] stream)
  obtain ⟨m, hm, hs⟩ := stream_eval current width left right (ProgramEncoding.encodeRecords alphabet)
    (TupleProgram.powerRows alphabet depth.length [[]]) stream hv
  have he : Eval command (n + (5 + (10 + m)))
      (inputState current.flatten width left right alphabet depth stream)
      (outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)) :=
    hg.seq (hc.seq (hr.seq hs))
  exact ⟨n + (5 + (10 + m)) + 1, by dsimp [sourceBudget]; omega,
    compiled_halt_trace he 19 11⟩

theorem primitive_run (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool)
    (hv : ∀ bits ∈ TupleProgram.powerRows alphabet depth.length [[]],
      CollisionTupleProgram.validPayload current width.length left right bits) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget current.flatten width.length left right alphabet depth.length)
      (primitiveCfg program
        ((inputState current.flatten width left right alphabet depth stream).withPC (some program.entry)))
      (primitiveCfg program
        ((outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
          (CollisionTupleProgram.streamed current.flatten width.length left right
            (TupleProgram.powerRows alphabet depth.length [[]]) stream)).withPC none)) :=
  BitProgram.primitive_execution program (program_run current width left right alphabet depth stream hv)

/-- The generated tuples' schema is proved from the input word widths; no
assumption about a generated callback result is needed. -/
theorem program_run_uniform (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool)
    (hc : ∀ row ∈ current, row.length = width.length)
    (ha : ∀ row ∈ alphabet, row.length = width.length)
    (hl : ∀ i ∈ left, i < current.length + depth.length)
    (hr : ∀ i ∈ right, i < current.length + depth.length) :
    RunsIn program (sourceBudget current.flatten width.length left right alphabet depth.length)
      ((inputState current.flatten width left right alphabet depth stream).withPC (some program.entry))
      ((outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)).withPC none) :=
  program_run current width left right alphabet depth stream
    (generated_validPayload current alphabet width.length depth.length left right hc ha hl hr)

def tallyRegs : Fin 2 → Fin 10 := Fin.castAdd 8
def tallyPorts : Fin 2 → Fin 20 := fun i => if i = 0 then 11 else 18

theorem tallyRegs_injective : Function.Injective tallyRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)

theorem tallyPorts_injective : Function.Injective tallyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [tallyPorts]

abbrev tallyCommand : Cmd 10 20 :=
  .call (ProgramLinking.liftProgram UnaryTally.program tallyRegs tallyPorts)

def afterTally (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 11 []) 18
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩

theorem tally_eval (d : Data) :
    Eval tallyCommand (UnaryTally.steps (d.stacks 11)) d (afterTally d) := by
  let a : StructuredProgram.State 2 2 :=
    ⟨d.regs ∘ tallyRegs, UnaryTally.pairStacks (d.stacks 11) (d.stacks 18)⟩
  let b : StructuredProgram.State 2 2 :=
    ⟨fun _ => false, UnaryTally.pairStacks []
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩
  have ha : embedState tallyRegs tallyPorts d a = d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a, tallyPorts, UnaryTally.pairStacks]
    · intros; rfl
    · intros; rfl
  have hb : embedState tallyRegs tallyPorts d b = afterTally d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; fin_cases i <;> simp [b, afterTally, tallyRegs, readRegs]
    · intro i; fin_cases i <;> simp [b, afterTally, tallyPorts, UnaryTally.pairStacks]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [tallyRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [tallyRegs] using h.symm⟩
      simp [afterTally, readRegs, h0, h1]
    · intro j hj
      have h11 : j ≠ 11 := fun h => hj ⟨0, by simpa [tallyPorts] using h.symm⟩
      have h18 : j ≠ 18 := fun h => hj ⟨1, by simpa [tallyPorts] using h.symm⟩
      simp [afterTally, h11, h18]
  have ht : Trace UnaryTally.program (UnaryTally.steps (d.stacks 11))
      (a.withPC (some UnaryTally.program.entry)) (b.withPC none) :=
    UnaryTally.tally_trace (d.regs ∘ tallyRegs) (d.stacks 11) (d.stacks 18)
  have he := eval_call_lifted UnaryTally.program tallyRegs tallyPorts d
    tallyRegs_injective tallyPorts_injective ht
  exact (by simpa only [ha, hb, tallyCommand] using he)

abbrev scoreCommand : Cmd 10 20 := .seq (.call program) tallyCommand

abbrev scoreProgram : Program 10 20 (StructuredCalls.size scoreCommand + 1) :=
  StructuredCalls.compiled scoreCommand 19 18

def scoreState (current width : List Bool) (left right : List ℕ)
    (alphabet leaves : List Bool) : Data :=
  afterTally (outputState current width left right alphabet leaves)

@[simp] theorem scoreState_output (current width : List Bool) (left right : List ℕ)
    (alphabet leaves : List Bool) :
    (scoreState current width left right alphabet leaves).stacks 18 =
      UnaryCompare.encode (PaddedCompletion.trueCount leaves) := by
  simp [scoreState, afterTally, outputState, storedState, UnaryCompare.encode]

def scoreBudget (current : List Bool) (width : ℕ) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth : ℕ) : ℕ :=
  sourceBudget current width left right alphabet depth + 5 * alphabet.length ^ depth + 4

/-- One fixed routine generates every tuple, evaluates its collision, then
returns the exact successful-leaf count as unary data on stack 18. -/
theorem score_program_run (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth : List Bool)
    (hc : ∀ row ∈ current, row.length = width.length)
    (ha : ∀ row ∈ alphabet, row.length = width.length)
    (hl : ∀ i ∈ left, i < current.length + depth.length)
    (hr : ∀ i ∈ right, i < current.length + depth.length) :
    RunsIn scoreProgram (scoreBudget current.flatten width.length left right alphabet depth.length)
      ((inputState current.flatten width left right alphabet depth []).withPC (some scoreProgram.entry))
      ((scoreState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) [])).withPC none) := by
  obtain ⟨n, hn, ht⟩ := program_run_uniform current width left right alphabet depth [] hc ha hl hr
  let d := outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
    (CollisionTupleProgram.streamed current.flatten width.length left right
      (TupleProgram.powerRows alphabet depth.length [[]]) [])
  have he := (Eval.call program ht).seq (tally_eval d)
  have hlen : (d.stacks 11).length = alphabet.length ^ depth.length := by
    simp [d, outputState, storedState, CollisionTupleProgram.streamed_length,
      TupleProgram.generated_count]
  have hcost := UnaryTally.steps_le (d.stacks 11)
  rw [hlen] at hcost
  exact ⟨n + UnaryTally.steps (d.stacks 11) + 1, by dsimp [scoreBudget]; omega,
    compiled_halt_trace he 19 18⟩

theorem score_primitive_run (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth : List Bool)
    (hc : ∀ row ∈ current, row.length = width.length)
    (ha : ∀ row ∈ alphabet, row.length = width.length)
    (hl : ∀ i ∈ left, i < current.length + depth.length)
    (hr : ∀ i ∈ right, i < current.length + depth.length) :
    Computation.RunsIn (primitive scoreProgram).step
      (primitiveOverhead scoreProgram *
        scoreBudget current.flatten width.length left right alphabet depth.length)
      (primitiveCfg scoreProgram
        ((inputState current.flatten width left right alphabet depth []).withPC (some scoreProgram.entry)))
      (primitiveCfg scoreProgram
        ((scoreState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
          (CollisionTupleProgram.streamed current.flatten width.length left right
            (TupleProgram.powerRows alphabet depth.length [[]]) [])).withPC none)) :=
  BitProgram.primitive_execution scoreProgram
    (score_program_run current width left right alphabet depth hc ha hl hr)

end SubexponentialSAT.Subexp.CollisionGenerateProgram

end OAI.Algorithms
