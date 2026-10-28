import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Physical unary initialization of the retained-key width

The fixed program reads unary D on stack 2 and writes unary
I = (D + 2) * (2 * D + 2) on stack 3. It copies D to build the
two factors, then executes one preserving copy of the second factor for
each token of the first. Stacks 0, 1, and 4 are restored empty.
-/

namespace SubexponentialSAT.SubexpIndexWidthProgram

open BitProgram StructuredProgram StructuredCalls

abbrev Data := StructuredProgram.State 3 5
abbrev Code := StructuredCalls.Cmd 3 5

def unary (n : ℕ) : List Bool := List.replicate n true

def copy (source target : Fin 5) : Code :=
  .call (StackRoutines.copyProgram source target 4 0 1)

def copied (source target : Fin 5) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks source target d.stacks⟩

theorem copy_eval (source target : Fin 5) (d : Data)
    (hst : source ≠ target) (hs4 : source ≠ 4) (h4t : (4 : Fin 5) ≠ target)
    (h4 : d.stacks 4 = []) :
    Eval (copy source target) (7 * (d.stacks source).length + 5)
      d (copied source target d) :=
  .call _ (ListRegisterProgram.copy_run source target 4 0 1
    hst hs4 h4t (by decide) d.regs d.stacks h4)

theorem copied_frame (source target : Fin 5) (d : Data) (i : Fin 5)
    (hi : i ≠ target) : (copied source target d).stacks i = d.stacks i := by
  simp [copied, StackRoutines.copyStacks, hi]

def pushTwo (target : Fin 5) : Code :=
  .base (.seq (.atom (.set 0 true))
    (.seq (.atom (.push target 0)) (.atom (.push target 0))))

def pushedTwo (target : Fin 5) (d : Data) : Data :=
  ⟨Function.update d.regs 0 true,
    Function.update d.stacks target (true :: true :: d.stacks target)⟩

theorem pushTwo_eval (target : Fin 5) (d : Data) :
    Eval (pushTwo target) 3 d (pushedTwo target d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) d).seq
    ((StructuredProgram.Eval.atom (.push target 0) _).seq
      (StructuredProgram.Eval.atom (.push target 0) _))
  exact .base (by simpa [pushedTwo, Atom.eval, Atom.instr, State.ofCfg,
    State.withPC, execInstr] using h)

def clearOne : Code := .call (StackRoutines.clearProgram 1 0 1)

def clearedOne (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 1 []⟩

theorem clearOne_eval (d : Data) :
    Eval clearOne (2 * (d.stacks 1).length + 3) d (clearedOne d) :=
  .call _ (ListRegisterProgram.clear_run 1 0 1 d.regs d.stacks)

def prepare : Code :=
  .seq (copy 2 0) (.seq (pushTwo 0)
    (.seq (copy 2 1) (.seq (copy 2 1) (pushTwo 1))))

def prepared (d : Data) : Data :=
  pushedTwo 1 (copied 2 1 (copied 2 1 (pushedTwo 0 (copied 2 0 d))))

def Ready (D : ℕ) (d : Data) : Prop :=
  d.stacks 2 = unary D ∧ d.stacks 0 = [] ∧ d.stacks 1 = [] ∧
    d.stacks 3 = [] ∧ d.stacks 4 = []

theorem prepared_words (D : ℕ) (d : Data) (hd : Ready D d) :
    (prepared d).stacks 0 = unary (D + 2) ∧
    (prepared d).stacks 1 = unary (2 * D + 2) ∧
    (prepared d).stacks 2 = d.stacks 2 ∧
    (prepared d).stacks 3 = [] ∧ (prepared d).stacks 4 = [] := by
  rcases hd with ⟨hD, h0, h1, h3, h4⟩
  simp [prepared, copied, StackRoutines.copyStacks, pushedTwo, hD, h0, h1, h3, h4,
    unary, List.replicate_succ, Nat.two_mul]

theorem prepare_eval (D : ℕ) (d : Data) (hd : Ready D d) :
    Eval prepare (21 * D + 21) d (prepared d) := by
  rcases hd with ⟨hD, h0, h1, h3, h4⟩
  let a := copied 2 0 d
  let b := pushedTwo 0 a
  let c := copied 2 1 b
  let e := copied 2 1 c
  have ha4 : a.stacks 4 = [] := (copied_frame 2 0 d 4 (by decide)).trans h4
  have hb4 : b.stacks 4 = [] := by simpa [b, pushedTwo] using ha4
  have hc4 : c.stacks 4 = [] := (copied_frame 2 1 b 4 (by decide)).trans hb4
  have hb2 : b.stacks 2 = unary D := by
    simpa [b, a, pushedTwo, copied, StackRoutines.copyStacks] using hD
  have hc2 : c.stacks 2 = unary D := (copied_frame 2 1 b 2 (by decide)).trans hb2
  have hfirst := copy_eval 2 0 d (by decide) (by decide) (by decide) h4
  have hsecond := copy_eval 2 1 b (by decide) (by decide) (by decide) hb4
  have hthird := copy_eval 2 1 c (by decide) (by decide) (by decide) hc4
  simp only [hD, hb2, hc2, unary, List.length_replicate] at hfirst hsecond hthird
  have he := hfirst.seq ((pushTwo_eval 0 a).seq
    (hsecond.seq (hthird.seq (pushTwo_eval 1 e))))
  convert he using 1 <;> first | rfl | ring

def loopPorts : UnaryForPrograms.Ports 3 5 := ⟨0, 0, 1⟩
def multiply : Code := UnaryForPrograms.forCmd loopPorts (copy 1 3)

def Frame (base d : Data) : Prop :=
  ∀ i : Fin 5, i ≠ 0 → i ≠ 3 → d.stacks i = base.stacks i

def LoopInvariant (base : Data) (B i : ℕ) (d : Data) : Prop :=
  Frame base d ∧ d.stacks 3 = unary (i * B)

theorem loop_stable (base : Data) (B : ℕ) :
    UnaryForPrograms.FrameStable loopPorts (LoopInvariant base B) := by
  intro i a b hab hi
  constructor
  · intro j hj0 hj3
    exact (hab j hj0).symm.trans (hi.1 j hj0 hj3)
  · exact (hab 3 (by decide)).symm.trans hi.2

theorem loop_body (base : Data) (B : ℕ)
    (hB : base.stacks 1 = unary B) (h4 : base.stacks 4 = []) :
    UnaryForPrograms.BodySpec loopPorts (copy 1 3) (LoopInvariant base B)
      (fun _ => 7 * B + 5) := by
  intro i d hi
  have hd1 := (hi.1 1 (by decide) (by decide)).trans hB
  have hd4 := (hi.1 4 (by decide) (by decide)).trans h4
  have he := copy_eval 1 3 d (by decide) (by decide) (by decide) hd4
  simp only [hd1, unary, List.length_replicate] at he
  refine ⟨7 * B + 5, copied 1 3 d, le_rfl, he,
    copied_frame 1 3 d 0 (by decide), ?_⟩
  constructor
  · intro j hj0 hj3
    exact (copied_frame 1 3 d j hj3).trans (hi.1 j hj0 hj3)
  · change (StackRoutines.copyStacks 1 3 d.stacks) 3 = _
    rw [StackRoutines.copyStacks_dst, hd1, hi.2]
    rw [show (i + 1) * B = B + i * B by ring]
    exact (List.replicate_add B (i * B) true).symm

theorem multiply_eval (A B : ℕ) (d : Data)
    (hA : d.stacks 0 = unary A) (hB : d.stacks 1 = unary B)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ t e, Eval multiply t d e ∧ Frame d e ∧
      e.stacks 0 = [] ∧ e.stacks 3 = unary (A * B) ∧
      t ≤ A * (7 * B + 7) + 2 := by
  have hi : LoopInvariant d B 0 d := ⟨fun _ _ _ => rfl, by simpa [unary] using h3⟩
  obtain ⟨t, e, he, hinv, hzero, ht⟩ := UnaryForPrograms.for_correct
    loopPorts (copy 1 3) (LoopInvariant d B) (fun _ => 7 * B + 5)
    (loop_stable d B) (loop_body d B hB h4) d hi
  have hlen : (d.stacks loopPorts.counter).length = A := by simp [loopPorts, hA, unary]
  rw [hlen] at hinv ht
  rw [CounterForPrograms.budgetSum_const] at ht
  refine ⟨t, e, he, hinv.1, hzero, hinv.2, ?_⟩
  nlinarith

def command : Code := .seq prepare (.seq multiply clearOne)
def program := StructuredCalls.compiled command 2 3
def runtimeBound (D : ℕ) : ℕ := 100 * (D + 1)^2 + 1

theorem program_labels : StructuredCalls.size command + 1 = 45 := by decide

/-- Every output token is physically pushed by the preserving-copy loop. -/
theorem command_eval (D : ℕ) (d : Data) (hd : Ready D d) :
    ∃ t e, Eval command t d e ∧ t ≤ 100 * (D + 1)^2 ∧
      e.stacks = Function.update d.stacks 3 (unary (SubexpSymbolicCost.indexBits D)) := by
  obtain ⟨hA, hB, hD, h3, h4⟩ := prepared_words D d hd
  obtain ⟨t, e, he, hf, he0, he3, ht⟩ :=
    multiply_eval (D + 2) (2 * D + 2) (prepared d) hA hB h3 h4
  have he1 := (hf 1 (by decide) (by decide)).trans hB
  have hclear := clearOne_eval e
  simp only [he1, unary, List.length_replicate] at hclear
  have hall := (prepare_eval D d hd).seq (he.seq hclear)
  refine ⟨_, clearedOne e, hall, ?_, ?_⟩
  · nlinarith
  · funext i
    fin_cases i
    · simpa [clearedOne, hd.2.1] using he0
    · simp [clearedOne, hd.2.2.1]
    · simpa [clearedOne] using (hf 2 (by decide) (by decide)).trans hD
    · simpa [clearedOne, SubexpSymbolicCost.indexBits] using he3
    · simpa [clearedOne, hd.2.2.2.2] using (hf 4 (by decide) (by decide)).trans h4

theorem run (D : ℕ) (d : Data) (hd : Ready D d) :
    ∃ e : Data, RunsIn program (runtimeBound D)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 3 (unary (SubexpSymbolicCost.indexBits D)) := by
  obtain ⟨t, e, he, ht, hs⟩ := command_eval D d hd
  exact ⟨e, ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 2 3⟩, hs⟩

theorem primitive_run (D : ℕ) (d : Data) (hd : Ready D d) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * runtimeBound D)
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update d.stacks 3 (unary (SubexpSymbolicCost.indexBits D)) := by
  obtain ⟨e, he, hs⟩ := run D d hd
  exact ⟨e, BitProgram.primitive_execution program he, hs⟩

/-- Empty unary input still produces the four-token retained-key width. -/
theorem run_zero (d : Data) (hd : Ready 0 d) :
    ∃ e : Data, RunsIn program 101
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 3 [true, true, true, true] := by
  simpa [runtimeBound, unary, SubexpSymbolicCost.indexBits] using run 0 d hd

/-- Arbitrary fixed injective placement changes only the caller's output port. -/
theorem lifted_output {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 5 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (D : ℕ) (a : StructuredProgram.State R S)
    (hD : a.stacks (stack 2) = unary D)
    (h0 : a.stacks (stack 0) = []) (h1 : a.stacks (stack 1) = [])
    (h3 : a.stacks (stack 3) = []) (h4 : a.stacks (stack 4) = []) :
    ∃ t b, t ≤ runtimeBound D ∧
      Eval (.call (ProgramLinking.liftProgram program register stack)) t a b ∧
      b.stacks = Function.update a.stacks (stack 3) (unary (SubexpSymbolicCost.indexBits D)) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  let d : Data := ⟨a.regs ∘ register, a.stacks ∘ stack⟩
  have hd : Ready D d := ⟨hD, h0, h1, h3, h4⟩
  obtain ⟨t, e, he, ht, hw⟩ := command_eval D d hd
  have hstart : embedState register stack a d = a := by
    apply embedState_eq_of_ports _ _ _ _ _ hr hs <;> intros <;> rfl
  have hc := eval_call_lifted program register stack a hr hs (compiled_halt_trace he 2 3)
  rw [hstart] at hc
  refine ⟨t + 1, embedState register stack a e, Nat.add_le_add_right ht 1, hc, ?_, ?_⟩
  · funext i
    by_cases hit : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hit
      rw [embedState_stack register stack a e hs, hw]
      simp [Function.update_apply, hs.eq_iff, d]
    · rw [embedState_stack_frame register stack a e i hit]
      have hi : i ≠ stack 3 := fun h => hit ⟨3, h.symm⟩
      simp [Function.update_of_ne hi]
  · exact fun i hi => embedState_register_frame register stack a e i hi

end SubexponentialSAT.SubexpIndexWidthProgram

end OAI.Algorithms
