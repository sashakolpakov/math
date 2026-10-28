import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Actual nested unary U/Z enumeration

The master unary word on stack 2 determines D. The fixed program invokes its
callback with u = 0,...,D for each z = 0,...,D-1. Counter words are copied at
runtime; their lengths never alter the finite instruction table. Callbacks
may clobber every register and update output stack 14. All other stacks are
restored, including the four initially empty controller stacks.
-/

namespace SubexponentialSAT.UnaryGridProgram

open BitProgram StructuredProgram StructuredCalls
open CounterForPrograms (budgetSum)

abbrev Data := StructuredProgram.State 3 24
abbrev Code := StructuredCalls.Cmd 3 24

def unary (n : ℕ) : List Bool := List.replicate n true

def innerPorts : UnaryForPrograms.Ports 3 24 := ⟨6, 0, 1⟩
def outerPorts : UnaryForPrograms.Ports 3 24 := ⟨7, 0, 1⟩

def push (target : Fin 24) : Code :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push target 0)))

def pushed (target : Fin 24) (d : Data) : Data :=
  ⟨Function.update d.regs 0 true,
    Function.update d.stacks target (true :: d.stacks target)⟩

theorem push_eval (target : Fin 24) (d : Data) :
    StructuredCalls.Eval (push target) 2 d (pushed target d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) d).seq
    (StructuredProgram.Eval.atom (.push target 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

def copyTo (target : Fin 24) : Code :=
  .call (StackRoutines.copyProgram 2 target 11 0 1)

def copied (target : Fin 24) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 target d.stacks⟩

theorem copy_eval (target : Fin 24) (d : Data)
    (h2 : (2 : Fin 24) ≠ target) (h11 : (11 : Fin 24) ≠ target)
    (hs : d.stacks 11 = []) :
    StructuredCalls.Eval (copyTo target) (7 * (d.stacks 2).length + 5) d (copied target d) :=
  .call _ (ListRegisterProgram.copy_run 2 target 11 0 1 h2 (by decide) h11
    (by decide) d.regs d.stacks hs)

def clear (target : Fin 24) : Code := .call (StackRoutines.clearProgram target 0 1)
def cleared (target : Fin 24) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target []⟩

theorem clear_eval (target : Fin 24) (d : Data) :
    StructuredCalls.Eval (clear target) (2 * (d.stacks target).length + 3)
      d (cleared target d) :=
  .call _ (ListRegisterProgram.clear_run target 0 1 d.regs d.stacks)

/-- The persistent context excludes the controller and output ports. -/
def Frame (base d : Data) : Prop :=
  ∀ j : Fin 24, j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 14 →
    d.stacks j = base.stacks j

theorem frame_refl (d : Data) : Frame d d := fun _ _ _ _ _ _ => rfl

theorem frame_update {base a b : Data} (h : Frame base a)
    (target : Fin 24) (word : List Bool)
    (ht : target = 4 ∨ target = 5 ∨ target = 6 ∨ target = 7 ∨ target = 14)
    (he : b.stacks = Function.update a.stacks target word) : Frame base b := by
  intro j h4 h5 h6 h7 h14
  have hj : j ≠ target := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> assumption
  rw [he, Function.update_of_ne hj]
  exact h j h4 h5 h6 h7 h14

theorem frame_master {base d : Data} (h : Frame base d) : d.stacks 2 = base.stacks 2 :=
  h 2 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem frame_scratch {base d : Data} (h : Frame base d) : d.stacks 11 = base.stacks 11 :=
  h 11 (by decide) (by decide) (by decide) (by decide) (by decide)

abbrev OutputStep := ℕ → ℕ → List Bool → List Bool

/-- The caller supplies executable callback correctness on the preserved
context. Every application includes an actual measured evaluation. -/
def CallbackSpec (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (base : Data) : Prop :=
  ∀ u z d, Frame base d → d.stacks 4 = unary u → d.stacks 5 = unary z →
    ∃ n e, n ≤ cost u z ∧ StructuredCalls.Eval body n d e ∧
      e.stacks = Function.update d.stacks 14 (step u z (d.stacks 14))

/-- These folds specify the observed callback order; the program never
evaluates them or any natural-number loop. -/
def rowOutput (step : OutputStep) (z : ℕ) : ℕ → List Bool → List Bool
  | 0, out => out
  | u + 1, out => step u z (rowOutput step z u out)

def gridOutput (step : OutputStep) (D : ℕ) : ℕ → List Bool → List Bool
  | 0, out => out
  | z + 1, out => rowOutput step z (D + 1) (gridOutput step D z out)

def innerBody (body : Code) : Code := .seq body (push 4)

structure InnerInvariant (step : OutputStep) (base start : Data) (z u : ℕ)
    (d : Data) : Prop where
  uWord : d.stacks 4 = unary u
  zWord : d.stacks 5 = unary z
  outerCount : d.stacks 7 = start.stacks 7
  output : d.stacks 14 = rowOutput step z u (start.stacks 14)
  frame : Frame base d

theorem inner_stable (step : OutputStep) (base start : Data) (z : ℕ) :
    UnaryForPrograms.FrameStable innerPorts (InnerInvariant step base start z) := by
  intro u a b hab hi
  refine ⟨(hab 4 (by decide)).symm.trans hi.uWord,
    (hab 5 (by decide)).symm.trans hi.zWord,
    (hab 7 (by decide)).symm.trans hi.outerCount,
    (hab 14 (by decide)).symm.trans hi.output, ?_⟩
  intro j h4 h5 h6 h7 h14
  exact (hab j h6).symm.trans (hi.frame j h4 h5 h6 h7 h14)

theorem inner_spec (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (base start : Data) (z : ℕ) (spec : CallbackSpec body step cost base) :
    UnaryForPrograms.BodySpec innerPorts (innerBody body)
      (InnerInvariant step base start z) (fun u => cost u z + 2) := by
  intro u d hi
  obtain ⟨n, e, hn, he, heq⟩ := spec u z d hi.frame hi.uWord hi.zWord
  refine ⟨n + 2, pushed 4 e, Nat.add_le_add_right hn 2,
    he.seq (push_eval 4 e), ?_, ?_⟩
  · simp [innerPorts, pushed, heq]
  · constructor
    · simp [pushed, heq, hi.uWord, unary, List.replicate_succ]
    · simpa [pushed, heq] using hi.zWord
    · simpa [pushed, heq] using hi.outerCount
    · simp [pushed, heq, hi.output, rowOutput]
    · exact frame_update (frame_update hi.frame 14 _ (by simp) heq)
        4 _ (by simp) rfl

def rowStart (d : Data) : Data := pushed 6 (copied 6 d)

def rowCmd (body : Code) : Code :=
  .seq (copyTo 6) (.seq (push 6)
    (.seq (UnaryForPrograms.forCmd innerPorts (innerBody body))
      (.seq (clear 4) (push 5))))

def rowBound (cost : ℕ → ℕ → ℕ) (D z : ℕ) : ℕ :=
  budgetSum (fun u => cost u z + 2) 0 (D + 1) + 11 * D + 18

/-- Recorded inner visits use the actual sequence callback;push-u. Thus
each visit contains the callback's measured execution and its two-step
increment, with no abstract callback event replacing machine execution. -/
def RowExecution (body : Code) (d e : Data) (costs : List ℕ) (n : ℕ) : Prop :=
  ∃ middle loopTicks,
    UnaryForPrograms.Visits innerPorts (innerBody body) costs loopTicks (rowStart d) middle ∧
    e = pushed 5 (cleared 4 middle) ∧
    n = (7 * (d.stacks 2).length + 5) +
      (2 + (loopTicks + ((2 * (middle.stacks 4).length + 3) + 2)))

theorem row_correct (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (base d : Data) (z : ℕ) (spec : CallbackSpec body step cost base)
    (hf : Frame base d) (hs : base.stacks 11 = [])
    (h4 : d.stacks 4 = []) (h6 : d.stacks 6 = []) (h5 : d.stacks 5 = unary z) :
    ∃ costs n e, RowExecution body d e costs n ∧
      StructuredCalls.Eval (rowCmd body) n d e ∧
      costs.length = (base.stacks 2).length + 1 ∧
      n ≤ rowBound cost (base.stacks 2).length z ∧
      e.stacks 4 = [] ∧ e.stacks 6 = [] ∧ e.stacks 5 = unary (z + 1) ∧
      e.stacks 7 = d.stacks 7 ∧
      e.stacks 14 = rowOutput step z ((base.stacks 2).length + 1) (d.stacks 14) ∧
      Frame base e := by
  have hd11 : d.stacks 11 = [] := (frame_scratch hf).trans hs
  have hd2 : d.stacks 2 = base.stacks 2 := frame_master hf
  have hstart : InnerInvariant step base d z 0 (rowStart d) := by
    constructor
    · simpa [rowStart, pushed, copied, StackRoutines.copyStacks, unary] using h4
    · simpa [rowStart, pushed, copied, StackRoutines.copyStacks] using h5
    · simp [rowStart, pushed, copied, StackRoutines.copyStacks]
    · simp [rowStart, pushed, copied, StackRoutines.copyStacks, rowOutput]
    · exact frame_update (frame_update hf 6 _ (by simp) rfl) 6 _ (by simp) rfl
  obtain ⟨costs, n, e, hv, he, hlen, hi, hempty, htime, hbudget⟩ :=
    UnaryForPrograms.for_correct_measured innerPorts (innerBody body)
      (InnerInvariant step base d z) (fun u => cost u z + 2)
      (inner_stable step base d z) (inner_spec body step cost base d z spec)
      (rowStart d) hstart
  have hcount : ((rowStart d).stacks innerPorts.counter).length =
      (base.stacks 2).length + 1 := by
    simp [rowStart, pushed, copied, StackRoutines.copyStacks, innerPorts, h6, hd2]
  rw [hcount] at hlen hi hbudget
  have h4len : (e.stacks 4).length = (base.stacks 2).length + 1 := by
    simp [hi.uWord, unary]
  let f := pushed 5 (cleared 4 e)
  let ticks := (7 * (d.stacks 2).length + 5) +
    (2 + (n + ((2 * (e.stacks 4).length + 3) + 2)))
  refine ⟨costs, ticks, f, ⟨e, n, hv, rfl, rfl⟩, ?_, hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (copy_eval 6 d (by decide) (by decide) hd11).seq
      ((push_eval 6 (copied 6 d)).seq
        (he.seq ((clear_eval 4 e).seq (push_eval 5 (cleared 4 e)))))
  · dsimp [ticks, rowBound]
    rw [hd2, h4len, htime, hlen]
    omega
  · simp [f, pushed, cleared]
  · simpa [f, pushed, cleared, innerPorts] using hempty
  · simp [f, pushed, cleared, hi.zWord, unary, List.replicate_succ]
  · simpa [f, pushed, cleared] using hi.outerCount
  · simpa [f, pushed, cleared] using hi.output
  · exact frame_update (frame_update hi.frame 4 _ (by simp) rfl) 5 _ (by simp) rfl

structure OuterInvariant (step : OutputStep) (base : Data) (z : ℕ) (d : Data) : Prop where
  uEmpty : d.stacks 4 = []
  zWord : d.stacks 5 = unary z
  innerEmpty : d.stacks 6 = []
  output : d.stacks 14 = gridOutput step (base.stacks 2).length z (base.stacks 14)
  frame : Frame base d

theorem outer_stable (step : OutputStep) (base : Data) :
    UnaryForPrograms.FrameStable outerPorts (OuterInvariant step base) := by
  intro z a b hab hi
  refine ⟨(hab 4 (by decide)).symm.trans hi.uEmpty,
    (hab 5 (by decide)).symm.trans hi.zWord,
    (hab 6 (by decide)).symm.trans hi.innerEmpty,
    (hab 14 (by decide)).symm.trans hi.output, ?_⟩
  intro j h4 h5 h6 h7 h14
  exact (hab j h7).symm.trans (hi.frame j h4 h5 h6 h7 h14)

theorem outer_spec (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (base : Data) (spec : CallbackSpec body step cost base) (hs : base.stacks 11 = []) :
    UnaryForPrograms.BodySpec outerPorts (rowCmd body) (OuterInvariant step base)
      (rowBound cost (base.stacks 2).length) := by
  intro z d hi
  obtain ⟨costs, n, e, hv, he, hlen, hn, h4, h6, h5, h7, hout, hf⟩ :=
    row_correct body step cost base d z spec hi.frame hs hi.uEmpty hi.innerEmpty hi.zWord
  refine ⟨n, e, hn, he, h7, h4, h5, h6, ?_, hf⟩
  simpa [gridOutput, hi.output] using hout

def command (body : Code) : Code :=
  .seq (copyTo 7) (.seq (UnaryForPrograms.forCmd outerPorts (rowCmd body)) (clear 5))

def gridBound (cost : ℕ → ℕ → ℕ) (D : ℕ) : ℕ :=
  budgetSum (rowBound cost D) 0 D + 11 * D + 10

/-- The measured outer visits each execute the complete inner enumeration.
The stack equality gives preservation of every non-output stack, including
the master counter and all initially empty work ports. -/
theorem grid_correct (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (d : Data) (spec : CallbackSpec body step cost d)
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h11 : d.stacks 11 = []) :
    ∃ costs n e,
      StructuredCalls.Eval (command body) n d e ∧
      costs.length = (d.stacks 2).length ∧
      (∃ loopTicks middle,
        UnaryForPrograms.Visits outerPorts (rowCmd body) costs loopTicks (copied 7 d) middle ∧
        e = cleared 5 middle ∧ n = (7 * (d.stacks 2).length + 5) +
          (loopTicks + (2 * (middle.stacks 5).length + 3))) ∧
      e.stacks = Function.update d.stacks 14
        (gridOutput step (d.stacks 2).length (d.stacks 2).length (d.stacks 14)) ∧
      n ≤ gridBound cost (d.stacks 2).length := by
  have hi0 : OuterInvariant step d 0 (copied 7 d) := by
    constructor
    · simpa [copied, StackRoutines.copyStacks] using h4
    · simpa [copied, StackRoutines.copyStacks, unary] using h5
    · simpa [copied, StackRoutines.copyStacks] using h6
    · simp [copied, StackRoutines.copyStacks, gridOutput]
    · exact frame_update (frame_refl d) 7 _ (by simp) rfl
  obtain ⟨costs, n, e, hv, he, hlen, hi, hempty, htime, hbudget⟩ :=
    UnaryForPrograms.for_correct_measured outerPorts (rowCmd body)
      (OuterInvariant step d) (rowBound cost (d.stacks 2).length)
      (outer_stable step d) (outer_spec body step cost d spec h11) (copied 7 d) hi0
  have hcount : ((copied 7 d).stacks outerPorts.counter).length = (d.stacks 2).length := by
    simp [copied, StackRoutines.copyStacks, outerPorts, h7]
  rw [hcount] at hlen hi hbudget
  have h5len : (e.stacks 5).length = (d.stacks 2).length := by simp [hi.zWord, unary]
  let ticks := (7 * (d.stacks 2).length + 5) + (n + (2 * (e.stacks 5).length + 3))
  refine ⟨costs, ticks, cleared 5 e,
    (copy_eval 7 d (by decide) (by decide) h11).seq (he.seq (clear_eval 5 e)),
    hlen, ⟨n, e, hv, rfl, rfl⟩, ?_, ?_⟩
  · funext j
    by_cases hj4 : j = 4
    · subst j; simp [cleared, hi.uEmpty, h4]
    by_cases hj5 : j = 5
    · subst j; simp [cleared, h5]
    by_cases hj6 : j = 6
    · subst j; simp [cleared, hi.innerEmpty, h6]
    by_cases hj7 : j = 7
    · subst j; simpa [cleared, h7, outerPorts] using hempty
    by_cases hj14 : j = 14
    · subst j; simpa [cleared] using hi.output
    · simpa [cleared, hj5, hj14] using hi.frame j hj4 hj5 hj6 hj7 hj14
  · dsimp [ticks, gridBound]
    rw [h5len, htime, hlen]
    omega

theorem budgetSum_le_constant (cost : ℕ → ℕ) (start fuel bound : ℕ)
    (h : ∀ i, start ≤ i → i < start + fuel → cost i ≤ bound) :
    budgetSum cost start fuel ≤ fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [budgetSum]
  | succ fuel ih =>
    have hhead : cost start ≤ bound := h start (by omega) (by omega)
    have htail := ih (start + 1) (by intro i hlo hhi; exact h i (by omega) (by omega))
    simp only [budgetSum]
    nlinarith

/-- A uniform callback bound yields an explicit polynomial controller cost. -/
theorem gridBound_le_uniform (cost : ℕ → ℕ → ℕ) (D B : ℕ)
    (h : ∀ u z, u ≤ D → z < D → cost u z ≤ B) :
    gridBound cost D ≤ D * (D + 1) * B + 13 * D ^ 2 + 31 * D + 10 := by
  have hrow : ∀ z, z < D → rowBound cost D z ≤ (D + 1) * (B + 2) + 11 * D + 18 := by
    intro z hz
    have hb := budgetSum_le_constant (fun u => cost u z + 2) 0 (D + 1) (B + 2)
      (by intro u _ hu; exact Nat.add_le_add_right (h u z (by omega) hz) 2)
    dsimp [rowBound]
    omega
  have hb := budgetSum_le_constant (rowBound cost D) 0 D
    ((D + 1) * (B + 2) + 11 * D + 18) (by intro z _ hz; exact hrow z (by omega))
  dsimp [gridBound]
  nlinarith

def program (body : Code) := StructuredCalls.compiled (command body) (2 : Fin 24) 14

@[simp] theorem command_size (body : Code) :
    StructuredCalls.size (command body) = StructuredCalls.size body + 34 := by
  simp [command, rowCmd, innerBody, copyTo, push, clear, StructuredCalls.size,
    StructuredProgram.size]
  omega

theorem program_runs (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (d : Data) (spec : CallbackSpec body step cost d)
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h11 : d.stacks 11 = []) :
    ∃ e : Data, BitProgram.RunsIn (program body) (gridBound cost (d.stacks 2).length + 1)
      (d.withPC (some (program body).entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 14
        (gridOutput step (d.stacks 2).length (d.stacks 2).length (d.stacks 14)) := by
  obtain ⟨costs, n, e, he, hlen, hv, heq, hn⟩ := grid_correct body step cost d spec h4 h5 h6 h7 h11
  exact ⟨e, ⟨n + 1, Nat.add_le_add_right hn 1, StructuredCalls.compiled_halt_trace he 2 14⟩, heq⟩

theorem program_primitive (body : Code) (step : OutputStep) (cost : ℕ → ℕ → ℕ)
    (d : Data) (spec : CallbackSpec body step cost d)
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = [])
    (h7 : d.stacks 7 = []) (h11 : d.stacks 11 = []) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive (program body)).step
      (BitProgram.primitiveOverhead (program body) * (gridBound cost (d.stacks 2).length + 1))
      (BitProgram.primitiveCfg (program body) (d.withPC (some (program body).entry)))
      (BitProgram.primitiveCfg (program body) (e.withPC none)) ∧
      e.stacks = Function.update d.stacks 14
        (gridOutput step (d.stacks 2).length (d.stacks 2).length (d.stacks 14)) := by
  obtain ⟨e, he, heq⟩ := program_runs body step cost d spec h4 h5 h6 h7 h11
  exact ⟨e, BitProgram.primitive_execution _ he, heq⟩

end SubexponentialSAT.UnaryGridProgram

end OAI.Algorithms
