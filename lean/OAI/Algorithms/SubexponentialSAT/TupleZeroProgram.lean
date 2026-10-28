import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-!
# Fixed-control construction of zero tuples

Counts and word widths are little-endian binary stack data. The output uses
Encoding.encodeList with its actual Boolean tags and frame delimiters. Both
loops are compiled from the checked binary-counter controller.
-/

namespace SubexponentialSAT.TupleZeroProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms CounterForPrograms

abbrev Data := StructuredProgram.State 13 9

def innerPorts : CounterForPrograms.Ports 13 9 where
  register := ⟨Fin.castAdd 10, by intro a b h; exact Fin.ext (congrArg (fun x : Fin 13 => x.val) h)⟩
  counter := 4
  scratch := 6
  counter_ne_scratch := by decide

def outerPorts : CounterForPrograms.Ports 13 9 where
  register := innerPorts.register
  counter := 1
  scratch := 6
  counter_ne_scratch := by decide

abbrev push (bit : Bool) : StructuredCalls.Cmd 13 9 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push 0 0)))

def pushed (bit : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks 0 (bit :: d.stacks 0)⟩

theorem push_eval (bit : Bool) (d : Data) :
    StructuredCalls.Eval (push bit) 2 d (pushed bit d) := by
  apply StructuredCalls.Eval.base
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 13) bit) d).seq
    (StructuredProgram.Eval.atom (.push (0 : Fin 9) 0) _)
  simpa [push, pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h

abbrev pair : StructuredCalls.Cmd 13 9 := .seq (push false) (push true)
def paired (d : Data) : Data := pushed true (pushed false d)

theorem pair_eval (d : Data) : StructuredCalls.Eval pair 4 d (paired d) :=
  (push_eval false d).seq (push_eval true (pushed false d))

abbrev clear (j : Fin 9) : StructuredCalls.Cmd 13 9 :=
  .call (StackRoutines.clearProgram j 0 1)
def cleared (j : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks j d.stacks⟩

theorem clear_eval (j : Fin 9) (d : Data) :
    StructuredCalls.Eval (clear j) (2 * (d.stacks j).length + 3) d (cleared j d) :=
  .call _ (ListRegisterProgram.clear_run j 0 1 d.regs d.stacks)

abbrev copyWidth : StructuredCalls.Cmd 13 9 :=
  .call (StackRoutines.copyProgram 2 4 5 0 1)
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 4 d.stacks⟩

theorem copyWidth_eval (d : Data) (hs : d.stacks 5 = []) :
    StructuredCalls.Eval copyWidth (7 * (d.stacks 2).length + 5) d (copied d) :=
  .call _ (ListRegisterProgram.copy_run 2 4 5 0 1 (by decide) (by decide)
    (by decide) (by decide) d.regs d.stacks hs)

/-- Only output and the selected controller's two ports may change. -/
def OutputInvariant (p : CounterForPrograms.Ports 13 9) (base : Data)
    (word : ℕ → List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 0 = word i ∧
    ∀ j : Fin 9, j ≠ 0 → j ≠ p.counter → j ≠ p.scratch → d.stacks j = base.stacks j

theorem outputInvariant_stable (p : CounterForPrograms.Ports 13 9)
    (hc : (0 : Fin 9) ≠ p.counter) (hs : (0 : Fin 9) ≠ p.scratch)
    (base : Data) (word : ℕ → List Bool) : FrameStable p (OutputInvariant p base word) := by
  intro i a b hab hi
  refine ⟨(hab 0 hc hs).symm.trans hi.1, ?_⟩
  intro j hj hcounter hscratch
  exact (hab j hcounter hscratch).symm.trans (hi.2 j hj hcounter hscratch)

def frameWord (base : Data) (i : ℕ) : List Bool :=
  Encoding.frame (List.replicate i false) ++ base.stacks 0

def innerInvariant (base : Data) := OutputInvariant innerPorts base (frameWord base)

theorem inner_initial (d : Data) : innerInvariant d 0 (pushed false d) := by
  constructor
  · simp [frameWord, Encoding.frame, pushed]
  · intro j hj _ _
    simp [pushed, hj]

theorem inner_spec (base : Data) : BodySpec innerPorts pair (innerInvariant base) (fun _ => 4) := by
  intro i d hi hs _
  refine ⟨4, paired d, le_rfl, pair_eval d, ?_, ?_, ?_⟩
  · simp [paired, pushed, innerPorts]
  · simpa [paired, pushed, innerPorts] using hs
  · constructor
    · change (paired d).stacks 0 = frameWord base (i + 1)
      have ho := hi.1
      change d.stacks 0 = frameWord base i at ho
      simp [paired, pushed, frameWord, List.replicate_succ, Encoding.frame, ho]
    · intro j hj hc hscratch
      simpa [paired, pushed, hj] using hi.2 j hj hc hscratch

abbrev frameZeros : StructuredCalls.Cmd 13 9 :=
  .seq (push false) (.seq (CounterForPrograms.forCmd innerPorts pair) (clear 4))

def frameBound (width : List Bool) : ℕ :=
  4 * value width + (value width + 1) * (16 * width.length + 16) + 2 * width.length + 5

/-- Consume the width on stack 4 and prepend an actual framed zero word.
The initial output may contain any suffix. -/
theorem frameZeros_correct (d : Data) (hs : d.stacks 6 = []) :
    ∃ n e, StructuredCalls.Eval frameZeros n d e ∧ n ≤ frameBound (d.stacks 4) ∧
      e.stacks = Function.update
        (Function.update d.stacks 0
          (Encoding.frame (List.replicate (value (d.stacks 4)) false) ++ d.stacks 0)) 4 [] := by
  obtain ⟨n, e, he, hi, hz, hw, hes, hn⟩ := CounterForPrograms.for_correct
    innerPorts pair (innerInvariant d) (fun _ => 4)
    (outputInvariant_stable innerPorts (by decide) (by decide) d (frameWord d))
    (inner_spec d) (pushed false d) (by simpa [pushed, innerPorts] using hs) (inner_initial d)
  have ho : e.stacks 0 = Encoding.frame (List.replicate (value (d.stacks 4)) false) ++
      d.stacks 0 := by simpa [innerPorts, pushed, frameWord] using hi.1
  have hf : ∀ j : Fin 9, j ≠ 0 → j ≠ 4 → j ≠ 6 → e.stacks j = d.stacks j := hi.2
  have hw' : (e.stacks 4).length = (d.stacks 4).length := by
    simpa [innerPorts, pushed] using hw
  have hs' : e.stacks 6 = [] := hes
  have hn' : n ≤ value (d.stacks 4) * 4 +
      (value (d.stacks 4) + 1) * (16 * (d.stacks 4).length + 16) := by
    simpa [innerPorts, pushed, budgetSum_const] using hn
  refine ⟨2 + (n + (2 * (e.stacks 4).length + 3)), cleared 4 e,
    (push_eval false d).seq (he.seq (clear_eval 4 e)), ?_, ?_⟩
  · dsimp [frameBound]
    rw [hw']
    omega
  · funext j
    fin_cases j
    · simp [cleared, StackRoutines.clearStacks, ho]
    · simp [cleared, StackRoutines.clearStacks, hf 1 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 2 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 3 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks]
    · simp [cleared, StackRoutines.clearStacks, hf 5 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hs', hs]
    · simp [cleared, StackRoutines.clearStacks, hf 7 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 8 (by decide) (by decide) (by decide)]


abbrev outerBody : StructuredCalls.Cmd 13 9 :=
  .seq copyWidth (.seq frameZeros (push true))

def outerBound (width : List Bool) : ℕ := 7 * width.length + 5 + (frameBound width + 2)

theorem outerBody_correct (d : Data) (h4 : d.stacks 4 = [])
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ n e, StructuredCalls.Eval outerBody n d e ∧ n ≤ outerBound (d.stacks 2) ∧
      e.stacks = Function.update d.stacks 0
        (true :: (Encoding.frame (List.replicate (value (d.stacks 2)) false) ++ d.stacks 0)) := by
  have hc := copyWidth_eval d h5
  have hc4 : (copied d).stacks 4 = d.stacks 2 := by
    simp [copied, StackRoutines.copyStacks, h4]
  have hc6 : (copied d).stacks 6 = [] := by
    simp [copied, StackRoutines.copyStacks, h6]
  obtain ⟨n, e, he, hn, hs⟩ := frameZeros_correct (copied d) hc6
  refine ⟨(7 * (d.stacks 2).length + 5) + (n + 2), pushed true e,
    hc.seq (he.seq (push_eval true e)), ?_, ?_⟩
  · rw [hc4] at hn
    dsimp [outerBound]
    omega
  · funext j
    fin_cases j <;> simp [pushed, hs, copied, StackRoutines.copyStacks, h4]

/-- Specification of repeated prefixing, not an executable natural-number loop. -/
def prependWord (rows : ℕ) (width : List Bool) (suffix : List Bool) : List Bool :=
  match rows with
  | 0 => suffix
  | n + 1 => true :: (Encoding.frame (List.replicate (value width) false) ++
      prependWord n width suffix)

theorem prependWord_encodeList (rows : ℕ) (width : List Bool) (tail : List (List Bool)) :
    prependWord rows width (Encoding.encodeList id tail) =
      Encoding.encodeList id (List.replicate rows (List.replicate (value width) false) ++ tail) := by
  induction rows with
  | zero => rfl
  | succ rows ih => simp [prependWord, List.replicate_succ, Encoding.encodeList, ih]

def outerInvariant (base : Data) := OutputInvariant outerPorts base
  (fun i => prependWord i (base.stacks 2) (base.stacks 0))

theorem outer_initial (d : Data) : outerInvariant d 0 d := by
  exact ⟨rfl, fun _ _ _ _ => rfl⟩

theorem outer_spec (base : Data) (h4 : base.stacks 4 = []) (h5 : base.stacks 5 = []) :
    BodySpec outerPorts outerBody (outerInvariant base) (fun _ => outerBound (base.stacks 2)) := by
  intro i d hi hs _
  have hd4 : d.stacks 4 = [] := (hi.2 4 (by decide) (by decide) (by decide)).trans h4
  have hd5 : d.stacks 5 = [] := (hi.2 5 (by decide) (by decide) (by decide)).trans h5
  have hd2 : d.stacks 2 = base.stacks 2 := hi.2 2 (by decide) (by decide) (by decide)
  obtain ⟨n, e, he, hn, heq⟩ := outerBody_correct d hd4 hd5 hs
  refine ⟨n, e, ?_, he, ?_, ?_, ?_⟩
  · simpa only [hd2] using hn
  · rw [heq]
    rfl
  · rw [heq]
    exact hs
  · constructor
    · change e.stacks 0 = prependWord (i + 1) (base.stacks 2) (base.stacks 0)
      rw [heq, Function.update_self, hd2, hi.1]
      rfl
    · intro j hj hc hscratch
      rw [heq, Function.update_of_ne hj]
      exact hi.2 j hj hc hscratch

/-- Preserve an existing serialized tail and prepend the requested zero records. -/
abbrev prependCommand : StructuredCalls.Cmd 13 9 :=
  .seq (CounterForPrograms.forCmd outerPorts outerBody) (.seq (clear 1) (clear 2))

def prependBound (rows width : List Bool) : ℕ :=
  value rows * outerBound width + (value rows + 1) * (16 * rows.length + 16) +
    2 * rows.length + 2 * width.length + 6

theorem prepend_correct (d : Data) (h4 : d.stacks 4 = [])
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ n e, StructuredCalls.Eval prependCommand n d e ∧
      n ≤ prependBound (d.stacks 1) (d.stacks 2) ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 0
        (prependWord (value (d.stacks 1)) (d.stacks 2) (d.stacks 0))) 1 []) 2 [] := by
  obtain ⟨n, e, he, hi, hz, hw, hs, hn⟩ := CounterForPrograms.for_correct
    outerPorts outerBody (outerInvariant d) (fun _ => outerBound (d.stacks 2))
    (outputInvariant_stable outerPorts (by decide) (by decide) d _)
    (outer_spec d h4 h5) d h6 (outer_initial d)
  have ho : e.stacks 0 = prependWord (value (d.stacks 1)) (d.stacks 2) (d.stacks 0) := hi.1
  have hf : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 6 → e.stacks j = d.stacks j := hi.2
  have hw' : (e.stacks 1).length = (d.stacks 1).length := hw
  have hw2 : (cleared 1 e).stacks 2 = d.stacks 2 := by
    simpa [cleared, StackRoutines.clearStacks] using hf 2 (by decide) (by decide) (by decide)
  have hs' : e.stacks 6 = [] := hs
  have hn' : n ≤ value (d.stacks 1) * outerBound (d.stacks 2) +
      (value (d.stacks 1) + 1) * (16 * (d.stacks 1).length + 16) := by
    simpa [outerPorts, budgetSum_const] using hn
  refine ⟨n + ((2 * (e.stacks 1).length + 3) +
      (2 * ((cleared 1 e).stacks 2).length + 3)), cleared 2 (cleared 1 e),
    he.seq ((clear_eval 1 e).seq (clear_eval 2 (cleared 1 e))), ?_, ?_⟩
  · rw [hw', hw2]
    dsimp [prependBound]
    omega
  · funext j
    fin_cases j
    · simp [cleared, StackRoutines.clearStacks, ho]
    · simp [cleared, StackRoutines.clearStacks]
    · simp [cleared, StackRoutines.clearStacks]
    · simp [cleared, StackRoutines.clearStacks, hf 3 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 4 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 5 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hs', h6]
    · simp [cleared, StackRoutines.clearStacks, hf 7 (by decide) (by decide) (by decide)]
    · simp [cleared, StackRoutines.clearStacks, hf 8 (by decide) (by decide) (by decide)]

/-- Standard empty-tail initialization, including zero rows or zero width. -/
def command : StructuredCalls.Cmd 13 9 := .seq (push false) prependCommand

def initialState (regs : Fin 13 → Bool) (rows width context : List Bool) : Data :=
  ⟨regs, ![[], rows, width, context, [], [], [], [], []]⟩

def finalState (regs : Fin 13 → Bool) (tuple context : List Bool) : Data :=
  ⟨regs, ![tuple, [], [], context, [], [], [], [], []]⟩

def output (rows width : List Bool) : List Bool :=
  Encoding.encodeList id (List.replicate (value rows) (List.replicate (value width) false))

theorem command_eval (regs : Fin 13 → Bool) (rows width context : List Bool) :
    ∃ n regs', StructuredCalls.Eval command n (initialState regs rows width context)
      (finalState regs' (output rows width) context) ∧ n ≤ prependBound rows width + 2 := by
  let d := initialState regs rows width context
  obtain ⟨n, e, he, hn, hs⟩ := prepend_correct (pushed false d)
    (by simp [pushed, d, initialState]) (by simp [pushed, d, initialState])
    (by simp [pushed, d, initialState])
  have ht : prependWord (value rows) width [false] = output rows width := by
    simpa [Encoding.encodeList, output] using prependWord_encodeList (value rows) width []
  have heq : e = finalState e.regs (output rows width) context := by
    apply CounterForPrograms.data_ext
    · rfl
    · rw [hs]
      funext j
      fin_cases j <;> simp [pushed, d, initialState, finalState, ht]
  refine ⟨2 + n, e.regs, ?_, ?_⟩
  · rw [← heq]
    exact (push_eval false d).seq he
  · have hn' : n ≤ prependBound rows width := by simpa [pushed, d, initialState] using hn
    omega

def runtimeBound (rows width : List Bool) : ℕ := prependBound rows width + 3

def program := StructuredCalls.compiled command (1 : Fin 9) 0

@[simp] theorem command_size : StructuredCalls.size command = 95 := by
  simp [command, prependCommand, outerBody, copyWidth, frameZeros, pair, push, clear,
    StructuredCalls.size, StructuredProgram.size]

theorem program_runs (regs : Fin 13 → Bool) (rows width context : List Bool) :
    ∃ regs', BitProgram.RunsIn program (runtimeBound rows width)
      ((initialState regs rows width context).withPC (some program.entry))
      ((finalState regs' (output rows width) context).withPC none) := by
  obtain ⟨n, regs', he, hn⟩ := command_eval regs rows width context
  refine ⟨regs', n + 1, ?_, StructuredCalls.compiled_halt_trace he 1 0⟩
  dsimp [runtimeBound]
  omega

theorem program_primitive (regs : Fin 13 → Bool) (rows width context : List Bool) :
    ∃ regs', Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * runtimeBound rows width)
      (BitProgram.primitiveCfg program ((initialState regs rows width context).withPC
        (some program.entry)))
      (BitProgram.primitiveCfg program ((finalState regs' (output rows width) context).withPC none)) := by
  obtain ⟨regs', h⟩ := program_runs regs rows width context
  exact ⟨regs', BitProgram.primitive_execution program h⟩

end SubexponentialSAT.TupleZeroProgram

end OAI.Algorithms
