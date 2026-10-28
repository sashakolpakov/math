import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
import OAI.Algorithms.SubexponentialSAT.ParserProgram

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

/-- Fixed Boolean control ports; all unbounded data live on bit stacks. -/
structure Ports (r : ℕ) where
  active : Fin r
  leaf : Fin r
  available : Fin r
  fresh : Fin r

/-- Each field is a finite instruction table, rather than a semantic oracle.
`ascend` restores the parent's cursor and advances it once. `descend` saves
the current cursor and starts the child at its first Boolean assignment. -/
structure Routines (r s : ℕ) where
  setup : Cmd r s
  probe : Cmd r s
  descend : Cmd r s
  advance : Cmd r s
  ascend : Cmd r s
  visit : Cmd r s

def body {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .ite p.leaf (.seq q.visit q.ascend)
    (.seq q.probe (.ite p.available (.ite p.fresh q.descend q.advance) q.ascend))

def loop {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .while p.active (body p q)

def command {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .seq q.setup (loop p q)

def program {r s : ℕ} (p : Ports r) (q : Routines r s)
    (inputStack outputStack : Fin s) : Program r s (size (command p q) + 1) :=
  compiled (command p q) inputStack outputStack

/-- Concrete cases of one interpreter iteration. Their costs include every
Boolean branch, including the fresh-signature test's losing case. -/
inductive Iteration {r s : ℕ} (p : Ports r) (q : Routines r s) :
    ℕ → State r s → State r s → Prop
  | leaf {a b c nv na} : a.regs p.leaf = true →
      Eval q.visit nv a b → Eval q.ascend na b c →
      Iteration p q (nv + na + 1) a c
  | fresh {a b c np nd} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = true → b.regs p.fresh = true →
      Eval q.descend nd b c → Iteration p q (np + nd + 3) a c
  | duplicate {a b c np nn} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = true → b.regs p.fresh = false →
      Eval q.advance nn b c → Iteration p q (np + nn + 3) a c
  | exhausted {a b c np na} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = false →
      Eval q.ascend na b c → Iteration p q (np + na + 2) a c

theorem Iteration.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Iteration p q n a b) : Eval (body p q) n a b := by
  cases h with
  | leaf hl hv ha => exact .ite_true hl (.seq hv ha)
  | fresh hl hp hb hf hd =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_true hf hd)))
  | duplicate hl hp hb hf hn =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_false hf hn)))
  | exhausted hl hp hb ha =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_false hb ha))

/-- Proof-level record of actual successive iterations; no trace is stored
by the executable program. The terminal guard test costs one step. -/
inductive Traversal {r s : ℕ} (p : Ports r) (q : Routines r s) :
    ℕ → State r s → State r s → Prop
  | done {a} : a.regs p.active = false → Traversal p q 1 a a
  | step {a b c n m} : a.regs p.active = true →
      Iteration p q n a b → Traversal p q m b c → Traversal p q (n + m + 1) a c

theorem Traversal.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Traversal p q n a b) : Eval (loop p q) n a b := by
  induction h with
  | done ha => exact .while_false ha
  | step ha hi _ ih => exact .while_true ha hi.eval ih

/-- The same initialized controller yields an actual halted source trace. -/
theorem program_trace {r s : ℕ} (p : Ports r) (q : Routines r s)
    (inputStack outputStack : Fin s) {ni nt : ℕ} {a b c : State r s}
    (hi : Eval q.setup ni a b) (ht : Traversal p q nt b c) :
    Trace (program p q inputStack outputStack) (ni + nt + 1)
      (a.withPC (some (program p q inputStack outputStack).entry)) (c.withPC none) :=
  compiled_halt_trace (.seq hi ht.eval) inputStack outputStack

/-- Every prefix of the actual fixed controller loop is covered. The body
bound must include suspended frames, all current words, and every scratch
stack; it must be proved uniformly before using this composition rule. -/
theorem traversal_stack_bound {r s : ℕ} (p : Ports r) (q : Routines r s)
    (inputStack outputStack : Fin s) (I : State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, Eval (body p q) n a b → I a →
      a.regs p.active = true → I b)
    (hbody : ∀ n a b, Eval (body p q) n a b → I a → a.regs p.active = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (compiled (body p q) inputStack outputStack) prefixSteps
          (a.withPC (some (compiled (body p q) inputStack outputStack).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : State r s} (ht : Traversal p q steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loop p q) inputStack outputStack) prefixSteps
        (a.withPC (some (compiled (loop p q) inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound :=
  StructuredSpace.loop_stack_bound (body p q) p.active inputStack outputStack I bound
    hinitial hpreserve hbody ht.eval ha

/-- Consume the current generator payload and prepend its escaped reverse to
the suspended-frame stack. The verified parser recovers the original order. -/
def pushFrameProgram : Program 2 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .push 1 0 5
    | 5 => .set 0 true 6
    | 6 => .push 1 0 2
    | _ => .halt

private theorem pushFrame_cycle (bit v present : Bool) (word frames : List Bool) :
    Trace pushFrameProgram 5
      (ParserProgram.cfg (some 2) v present (bit :: word) frames)
      (ParserProgram.cfg (some 2) true true word (true :: bit :: frames)) := by
  refine .cons (b := ParserProgram.cfg (some 3) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
  refine .cons (b := ParserProgram.cfg (some 4) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 5) bit true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 6) true true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)

private theorem pushFrame_loop (word saved frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 3)
      (ParserProgram.cfg (some 2) v present word (Encoding.frame saved ++ frames))
      (ParserProgram.cfg none false false []
        (Encoding.frame (word.reverse ++ saved) ++ frames)) := by
  induction word generalizing saved v present with
  | nil =>
      refine .cons (b := ParserProgram.cfg (some 3) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
      refine .cons (b := ParserProgram.cfg (some 7) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
      exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)
  | cons bit word ih =>
      have ht := (pushFrame_cycle bit v present word
        (Encoding.frame saved ++ frames)).trans (ih (bit :: saved) true true)
      have htime : 5 + (5 * word.length + 3) = 5 * (word.length + 1) + 3 := by omega
      simpa only [List.length_cons, htime, Encoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append] using ht

/-- Exact fixed-table suspension, including initialization and halt. -/
theorem pushFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 5)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
  have ht := pushFrame_loop word [] frames false present
  have ht' : Trace pushFrameProgram (5 * word.length + 3 + 1 + 1)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
    refine .cons (b := ParserProgram.cfg (some 1) false present word frames) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    refine .cons (b := ParserProgram.cfg (some 2) false present word (false :: frames)) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    simpa [Encoding.frame] using ht
  simpa only [Nat.add_assoc] using ht'

/-- Resume consumes one suspended frame and exactly restores its payload. -/
theorem popFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace ParserProgram.frameProgram (6 * word.length + 4)
      (ParserProgram.cfg (some 0) v present (Encoding.frame word.reverse ++ frames) [])
      (ParserProgram.cfg none false true frames word) := by
  simpa using ParserProgram.frame_trace word.reverse frames [] v present

/-- Suspended generator records only; no completed tuples or key family. -/
def suspendedFrames (frames : List (List Bool)) : List Bool :=
  frames.flatMap fun word => Encoding.frame word.reverse

theorem suspendedFrames_length_le (frames : List (List Bool)) (width levels : ℕ)
    (hdepth : frames.length ≤ levels)
    (hwidth : ∀ frame ∈ frames, frame.length ≤ width) :
    (suspendedFrames frames).length ≤ (2 * width + 1) * levels := by
  have h : (suspendedFrames frames).length ≤ (2 * width + 1) * frames.length := by
    induction frames with
    | nil => simp [suspendedFrames]
    | cons frame frames ih =>
        have hf := hwidth frame (by simp)
        have hh := ih (by simp only [List.length_cons] at hdepth; omega)
          (fun word hw => hwidth word (by simp [hw]))
        simp only [suspendedFrames, List.flatMap_cons, List.length_append,
          Encoding.length_frame, List.length_reverse, List.length_cons,
          Nat.mul_add, Nat.mul_one] at *
        omega
  exact h.trans (Nat.mul_le_mul_left _ hdepth)

/-- Local suspension uses linear time, so its every-prefix temporary space is
linear too. The persistent frame stack is included in the entry size. -/
theorem pushFrame_stack_bound (word frames : List Bool) (v present : Bool) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 5 * word.length + 5 →
      Trace pushFrameProgram prefixSteps
        (ParserProgram.cfg (some 0) v present word frames) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ frames.length + 6 * word.length + 5 := by
  have hb : dataBits (ParserProgram.cfg (some 0 : Option (Fin 8)) v present word frames) ≤
      word.length + frames.length := by
    simp [dataBits, stackBits, ParserProgram.cfg, Fin.sum_univ_two]
  have h := StructuredSpace.local_stack_bound pushFrameProgram
    (steps := 5 * word.length + 5) hb
  intro prefixSteps intermediate hle htrace i
  have hi := h prefixSteps intermediate hle htrace i
  omega

/-- Local resume includes every frame cell already present and the parser's
scratch/output cells at every source prefix. -/
theorem popFrame_stack_bound (word frames : List Bool) (v present : Bool) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 6 * word.length + 4 →
      Trace ParserProgram.frameProgram prefixSteps
        (ParserProgram.cfg (some 0) v present (Encoding.frame word.reverse ++ frames) [])
        intermediate →
      ∀ i, (intermediate.stacks i).length ≤ frames.length + 8 * word.length + 5 := by
  have hb : dataBits (ParserProgram.cfg (some 0 : Option (Fin 7)) v present
      (Encoding.frame word.reverse ++ frames) []) ≤ 2 * word.length + 1 + frames.length := by
    simp [dataBits, stackBits, ParserProgram.cfg, Fin.sum_univ_two]
  have h := StructuredSpace.local_stack_bound ParserProgram.frameProgram
    (steps := 6 * word.length + 4) hb
  intro prefixSteps intermediate hle htrace i
  have hi := h prefixSteps intermediate hle htrace i
  omega

/-- The shared leaf ABI reserves twelve fixed physical ports. Their order is
frames, representatives, candidate, key, payload, scratch, depth, limit,
predecessor, predecessor key, and two scratch buffers. -/
def tupleStacks : Fin 12 ↪ Fin 896 where
  toFun i := ⟨836 + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

def frameRegisters : Fin 2 ↪ Fin 40 := Fin.castLEEmb (by decide)

def framePushStacks : Fin 2 ↪ Fin 896 :=
  let fields : Fin 2 ↪ Fin 12 :=
    { toFun := fun i => if i = 0 then 4 else 0
      inj' := by decide }
  fields.trans tupleStacks

def framePopStacks : Fin 2 ↪ Fin 896 :=
  (Equiv.swap (0 : Fin 2) 1).toEmbedding.trans framePushStacks

/-- Both calls preserve every caller stack outside the two designated ports. -/
def suspendCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram pushFrameProgram frameRegisters framePushStacks)

def resumeCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram frameRegisters framePopStacks)

def frameState (v present : Bool) (src dst : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair v present, ParserProgram.pair src dst⟩

theorem suspend_eval (caller : State 40 896) (word frames : List Bool) (v present : Bool) :
    Eval suspendCommand (5 * word.length + 5)
      (embedState frameRegisters framePushStacks caller (frameState v present word frames))
      (embedState frameRegisters framePushStacks caller
        (frameState false false [] (Encoding.frame word.reverse ++ frames))) :=
  eval_call_lifted pushFrameProgram frameRegisters framePushStacks caller
    frameRegisters.injective framePushStacks.injective (pushFrame_trace word frames v present)

theorem resume_eval (caller : State 40 896) (word frames : List Bool) (v present : Bool) :
    Eval resumeCommand (6 * word.length + 4)
      (embedState frameRegisters framePopStacks caller
        (frameState v present (Encoding.frame word.reverse ++ frames) []))
      (embedState frameRegisters framePopStacks caller (frameState false true frames word)) :=
  eval_call_lifted ParserProgram.frameProgram frameRegisters framePopStacks caller
    frameRegisters.injective framePopStacks.injective (popFrame_trace word frames v present)

/-- The four controller flags are preserved by the smaller native routines.
Callbacks using the full register bank must use the shared caller-save wrapper. -/
def controllerPorts : Ports 40 := ⟨36, 37, 38, 39⟩

def candidatePorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 2
  scratch := tupleStacks 10
  counter_ne_scratch := by decide

def remainingPorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 7
  scratch := tupleStacks 5
  counter_ne_scratch := by decide

/-- One actual candidate advance. There is no construction of an assignment
list: both the cursor and remaining count are binary words. -/
def advanceCommand : Cmd 40 896 :=
  .seq (Counters.incrementCmd candidatePorts)
    (.seq (CounterForPrograms.advanceCmd remainingPorts)
      (.base (.atom (.copy controllerPorts.available (remainingPorts.register 2)))))

noncomputable def advanceState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.copy controllerPorts.available (remainingPorts.register 2)).eval
    (CounterForPrograms.nextState remainingPorts (Counters.incrementResult candidatePorts a))

def advanceTime (a : State 40 896) : ℕ :=
  (CounterPrograms.rippleCost true (a.stacks candidatePorts.counter) + 1) +
    (CounterForPrograms.advanceCost remainingPorts a + 1)

theorem advance_eval (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hrs : a.stacks remainingPorts.scratch = []) :
    Eval advanceCommand (advanceTime a) a (advanceState a) := by
  have hs : (Counters.incrementResult candidatePorts a).stacks remainingPorts.scratch = [] := by
    rw [Counters.incrementResult_stacks candidatePorts a hcs]
    rw [Function.update_of_ne (by decide : remainingPorts.scratch ≠ candidatePorts.counter)]
    exact hrs
  have he : (Counters.incrementResult candidatePorts a).stacks remainingPorts.counter =
      a.stacks remainingPorts.counter := by
    rw [Counters.incrementResult_stacks candidatePorts a hcs]
    exact Function.update_of_ne (by decide : remainingPorts.counter ≠ candidatePorts.counter) _ _
  have ht := Eval.seq (Counters.increment_eval candidatePorts a hcs)
    (Eval.seq (CounterForPrograms.advance_eval remainingPorts _ hs)
      (Eval.base (StructuredProgram.Eval.atom
        (.copy controllerPorts.available (remainingPorts.register 2)) _)))
  simpa only [advanceCommand, advanceTime, advanceState, CounterForPrograms.advanceCost, he]
    using ht

/-- The per-candidate overhead is polynomial in word widths, although the
represented remaining count can be exponential. -/
theorem advanceTime_le (a : State 40 896)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter)) :
    advanceTime a ≤ 8 * (a.stacks candidatePorts.counter).length +
      16 * (a.stacks remainingPorts.counter).length + 24 := by
  have hi := CounterPrograms.rippleCost_le true (a.stacks candidatePorts.counter)
  have hd := CounterForPrograms.advanceCost_le remainingPorts a hr
  unfold advanceTime
  omega

/-- Exhaustion is read from the full remaining word; no parity shortcut. -/
theorem advanceState_available (a : State 40 896) :
    (advanceState a).regs controllerPorts.available =
      !(CounterPrograms.isZero ((advanceState a).stacks remainingPorts.counter)) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).regs (remainingPorts.register 2) = _
  exact CounterForPrograms.nextState_flag _ _

theorem advanceState_candidate (a : State 40 896) :
    (advanceState a).stacks candidatePorts.counter =
      CounterPrograms.ripple true (a.stacks candidatePorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks candidatePorts.counter = _
  rw [← CounterForPrograms.nextState_outside remainingPorts
    (Counters.incrementResult candidatePorts a) candidatePorts.counter
    (by decide) (by decide)]
  exact Counters.incrementResult_counter _ _

theorem advanceState_remaining (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = []) :
    (advanceState a).stacks remainingPorts.counter =
      CounterPrograms.ripple false (a.stacks remainingPorts.counter) := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks remainingPorts.counter = _
  rw [CounterForPrograms.nextState_counter, Counters.incrementResult_stacks candidatePorts a hcs]
  rw [Function.update_of_ne (by decide : remainingPorts.counter ≠ candidatePorts.counter)]

/-- Cursor plus remaining fuel is unchanged by the actual candidate step. -/
theorem advanceState_total (a : State 40 896)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter)) :
    CounterPrograms.value ((advanceState a).stacks candidatePorts.counter) +
      CounterPrograms.value ((advanceState a).stacks remainingPorts.counter) =
      CounterPrograms.value (a.stacks candidatePorts.counter) +
        CounterPrograms.value (a.stacks remainingPorts.counter) := by
  rw [advanceState_candidate, advanceState_remaining a hcs, CounterPrograms.value_increment]
  have hd := CounterPrograms.value_decrement hr
  omega

/-- Binary words remain short even at the final overflow to the exact bound.
The exhausted word is never passed to the signature evaluator. -/
theorem advanceState_widths (a : State 40 896) (width : ℕ)
    (hcs : a.stacks candidatePorts.scratch = [])
    (hc : (a.stacks candidatePorts.counter).length ≤ width + 1)
    (hrlen : (a.stacks remainingPorts.counter).length ≤ width + 1)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter))
    (htotal : CounterPrograms.value (a.stacks candidatePorts.counter) +
      CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ width) :
    ((advanceState a).stacks candidatePorts.counter).length ≤ width + 1 ∧
      ((advanceState a).stacks remainingPorts.counter).length ≤ width + 1 := by
  constructor
  · rw [advanceState_candidate]
    apply CounterPrograms.increment_length_le_of_lt _ _ hc
    have hp : 0 < 2 ^ width := Nat.pow_pos (by decide)
    rw [pow_succ]
    omega
  · rw [advanceState_remaining a hcs, CounterPrograms.decrement_length hr]
    exact hrlen

/-- Every source prefix of the candidate advance includes the entire caller
frame. The added temporary storage is bounded by the two binary word widths. -/
theorem advance_stack_bound (a : State 40 896) (initialBound : ℕ)
    (hinit : stackBits a.stacks ≤ initialBound)
    (hr : 0 < CounterPrograms.value (a.stacks remainingPorts.counter)) :
    ∀ prefixSteps intermediate, prefixSteps ≤ advanceTime a →
      Trace (compiled advanceCommand 0 0) prefixSteps
        (a.withPC (some (compiled advanceCommand 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ initialBound +
        8 * (a.stacks candidatePorts.counter).length +
        16 * (a.stacks remainingPorts.counter).length + 24 := by
  have h := StructuredSpace.local_stack_bound (compiled advanceCommand 0 0)
    (a := a.withPC (some (compiled advanceCommand 0 0).entry))
    (steps := advanceTime a) hinit
  intro prefixSteps intermediate hle htrace i
  have hi := h prefixSteps intermediate hle htrace i
  have ht := advanceTime_le a hr
  omega

/-- Preserving copy uses one fixed empty scratch stack and two low registers. -/
def copyWord (src dst tmp : Fin 896) : Cmd 40 896 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

def copyState (src dst : Fin 896) (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

/-- The prepared head's unary size is copied as an all-zero initial assignment.
The length witness is consumed to initialize the binary remaining count. -/
def initialFuelPorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 4
  scratch := tupleStacks 7
  counter_ne_scratch := by decide

def initialFuelCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram Counters.powerTwoProgram
    initialFuelPorts.register (CounterForPrograms.stackPorts initialFuelPorts))

noncomputable def initialFuelState (a : State 40 896) : State 40 896 :=
  CounterForPrograms.install initialFuelPorts a false false (a.regs 2) []
    (List.replicate (a.stacks initialFuelPorts.counter).length false ++ [true])

theorem initialFuel_eval (a : State 40 896)
    (he : a.stacks initialFuelPorts.scratch = []) :
    Eval initialFuelCommand (4 * (a.stacks initialFuelPorts.counter).length + 5) a
      (initialFuelState a) := by
  have ht := eval_call_lifted Counters.powerTwoProgram initialFuelPorts.register
    (CounterForPrograms.stackPorts initialFuelPorts) a initialFuelPorts.register.injective
    (CounterForPrograms.stackPorts initialFuelPorts).injective
    (Counters.powerTwo_trace (a.stacks initialFuelPorts.counter)
      (a.regs (initialFuelPorts.register 0)) (a.regs (initialFuelPorts.register 1))
      (a.regs (initialFuelPorts.register 2)))
  change Eval initialFuelCommand _
    (CounterForPrograms.install initialFuelPorts a _ _ _ _ []) (initialFuelState a) at ht
  rw [← he, CounterForPrograms.install_self] at ht
  exact ht

def resetCommand : Cmd 40 896 :=
  .seq (copyWord 651 (tupleStacks 2) (tupleStacks 5))
    (.seq (copyWord 651 (tupleStacks 4) (tupleStacks 5))
      (.seq initialFuelCommand
        (.seq (.base (.atom (.set controllerPorts.available true)))
          (.base (.atom (.set controllerPorts.fresh false))))))

noncomputable def resetState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.fresh false).eval
    ((StructuredProgram.Atom.set controllerPorts.available true).eval
      (initialFuelState (copyState 651 (tupleStacks 4)
        (copyState 651 (tupleStacks 2) a))))

theorem reset_eval (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (he : a.stacks (tupleStacks 7) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    Eval resetCommand (18 * h + 17) a (resetState a) := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  have hb := copyWord_eval 651 (tupleStacks 2) (tupleStacks 5)
    (by decide) (by decide) (by decide) a ht
  have hbt : b.stacks (tupleStacks 5) = [] := by
    simpa [b, copyState, StackRoutines.copyStacks] using ht
  have hc := copyWord_eval 651 (tupleStacks 4) (tupleStacks 5)
    (by decide) (by decide) (by decide) b hbt
  have hce : c.stacks initialFuelPorts.scratch = [] := by
    simpa [c, b, copyState, StackRoutines.copyStacks, initialFuelPorts] using he
  have hi := initialFuel_eval c hce
  have hall := Eval.seq hb (Eval.seq hc (Eval.seq hi
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom
      (.set controllerPorts.available true) _))
      (Eval.base (StructuredProgram.Eval.atom (.set controllerPorts.fresh false) _)))))
  have hbword : b.stacks 651 = List.replicate h false := by
    have hne : (651 : Fin 896) ≠ tupleStacks 2 := by decide
    simpa [b, copyState, StackRoutines.copyStacks, hne] using hw
  have hcpayload : c.stacks initialFuelPorts.counter =
      List.replicate h false := by
    change b.stacks 651 ++ b.stacks (tupleStacks 4) = _
    rw [hbword]
    have hbpayload : b.stacks (tupleStacks 4) = [] := by
      simpa [b, copyState, StackRoutines.copyStacks] using hp
    simp only [hbpayload, List.append_nil]
  change Eval resetCommand _ a (resetState a) at hall
  convert hall using 1
  simp only [hw, hbword, hcpayload, List.length_replicate]
  omega

/-- Empty heads are initialized with the sole empty assignment and fuel one. -/
theorem resetState_words (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = List.replicate h false ∧
      (resetState a).stacks (tupleStacks 7) = List.replicate h false ++ [true] ∧
      (resetState a).stacks (tupleStacks 4) = [] := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  have hbsource : b.stacks 651 = List.replicate h false := by
    have hne : (651 : Fin 896) ≠ tupleStacks 2 := by decide
    simpa [b, copyState, StackRoutines.copyStacks, hne] using hw
  have hcpayload : c.stacks (tupleStacks 4) = List.replicate h false := by
    change b.stacks 651 ++ b.stacks (tupleStacks 4) = _
    rw [hbsource]
    have hp' : b.stacks (tupleStacks 4) = [] := by
      simpa [b, copyState, StackRoutines.copyStacks] using hp
    simp only [hp', List.append_nil]
  have hccandidate : c.stacks (tupleStacks 2) = List.replicate h false := by
    simp [c, b, copyState, StackRoutines.copyStacks, hc, hw]
  constructor
  · change (initialFuelState c).stacks (tupleStacks 2) = _
    unfold initialFuelState
    rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _
      (tupleStacks 2) (by decide) (by decide)]
    exact hccandidate
  constructor
  · change (CounterForPrograms.install initialFuelPorts c _ _ _ _ _).stacks
      initialFuelPorts.scratch = _
    rw [CounterForPrograms.install_scratch]
    change List.replicate (c.stacks (tupleStacks 4)).length false ++ [true] = _
    simp only [hcpayload, List.length_replicate]
  · exact CounterForPrograms.install_counter initialFuelPorts c _ _ _ _ _

theorem resetState_flags (a : State 40 896) :
    (resetState a).regs controllerPorts.available = true ∧
      (resetState a).regs controllerPorts.fresh = false := by
  simp [resetState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, controllerPorts]

/-- The reset creates the exact exponential fuel as a word of length `h+1`.
Its numeric value is used only in the proof, never as an executable loop list. -/
theorem resetState_values (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    CounterPrograms.value ((resetState a).stacks (tupleStacks 2)) = 0 ∧
      CounterPrograms.value ((resetState a).stacks (tupleStacks 7)) = 2 ^ h ∧
      ((resetState a).stacks (tupleStacks 2)).length = h ∧
      ((resetState a).stacks (tupleStacks 7)).length = h + 1 := by
  obtain ⟨hword, hfuel, _⟩ := resetState_words a h hw hc hp
  rw [hword, hfuel]
  simp only [ExecCNFTupleEnumeration.value_replicate_false, Counters.powerTwo_value,
    List.length_replicate, List.length_append, List.length_singleton, and_self]

/-- Reset's bound is uniform over all actual source prefixes, including the
persistent frame and representative stacks in the caller's entry storage. -/
theorem reset_stack_bound (a : State 40 896) (h initialBound : ℕ)
    (hinit : stackBits a.stacks ≤ initialBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 18 * h + 17 →
      Trace (compiled resetCommand 0 0) prefixSteps
        (a.withPC (some (compiled resetCommand 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ initialBound + 18 * h + 17 := by
  have hb := StructuredSpace.local_stack_bound (compiled resetCommand 0 0)
    (a := a.withPC (some (compiled resetCommand 0 0).entry))
    (steps := 18 * h + 17) hinit
  simpa only [Nat.add_assoc] using hb

/-- Two physical stack ports for a frame operation. -/
def wordPorts (src dst : Fin 896) (h : src ≠ dst) : Fin 2 ↪ Fin 896 where
  toFun i := if i = 0 then src else dst
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ he => congrArg g he) g a
  · exact Function.extend_apply' _ _ _ h

private theorem word_embed_self (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) :
    embedState frameRegisters (wordPorts src dst h) a
      (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)) = a := by
  apply CounterForPrograms.data_ext
  · have hr : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).regs =
        a.regs ∘ frameRegisters := by
      funext i
      fin_cases i <;> rfl
    change Function.extend frameRegisters _ a.regs = a.regs
    rw [hr, extend_restrict_eq]
  · have hs : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).stacks =
        a.stacks ∘ wordPorts src dst h := by
      funext i
      fin_cases i <;> rfl
    change Function.extend (wordPorts src dst h) _ a.stacks = a.stacks
    rw [hs, extend_restrict_eq]

def pushWordCommand (src dst : Fin 896) (h : src ≠ dst) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram pushFrameProgram frameRegisters (wordPorts src dst h))

noncomputable def pushWordState (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) : State 40 896 :=
  embedState frameRegisters (wordPorts src dst h) a
    (frameState false false [] (Encoding.frame (a.stacks src).reverse ++ a.stacks dst))

theorem pushWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    Eval (pushWordCommand src dst h) (5 * (a.stacks src).length + 5) a
      (pushWordState src dst h a) := by
  have ht := eval_call_lifted pushFrameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst))
    (b := frameState false false [] (Encoding.frame (a.stacks src).reverse ++ a.stacks dst))
    (pushFrame_trace (a.stacks src) (a.stacks dst) (a.regs 0) (a.regs 1))
  rw [word_embed_self] at ht
  exact ht

theorem pushWordState_src (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks src = [] :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem pushWordState_dst (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks dst =
      Encoding.frame (a.stacks src).reverse ++ a.stacks dst :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem pushWordState_outside (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (pushWordState src dst h a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

def popWordCommand (src dst : Fin 896) (h : src ≠ dst) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram frameRegisters (wordPorts src dst h))

noncomputable def popWordState (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) : State 40 896 :=
  embedState frameRegisters (wordPorts src dst h) a (frameState false true tail word)

theorem popWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (word tail : List Bool) (hs : a.stacks src = Encoding.frame word.reverse ++ tail)
    (hd : a.stacks dst = []) :
    Eval (popWordCommand src dst h) (6 * word.length + 4) a
      (popWordState src dst h a word tail) := by
  have ht := eval_call_lifted ParserProgram.frameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (Encoding.frame word.reverse ++ tail) [])
    (b := frameState false true tail word)
    (popFrame_trace word tail (a.regs 0) (a.regs 1))
  rw [← hs, ← hd, word_embed_self] at ht
  exact ht

theorem popWordState_src (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks src = tail :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem popWordState_dst (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks dst = word :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem popWordState_outside (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (popWordState src dst h a word tail).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

/-- A suspended head retains exactly its cursor and remaining count. Matrix
rows and keys are reconstructed when the head resumes. -/
def saveCursorCommand : Cmd 40 896 :=
  .seq (pushWordCommand (tupleStacks 2) (tupleStacks 0) (by decide))
    (pushWordCommand (tupleStacks 7) (tupleStacks 0) (by decide))

noncomputable def saveCursorState (a : State 40 896) : State 40 896 :=
  pushWordState (tupleStacks 7) (tupleStacks 0) (by decide)
    (pushWordState (tupleStacks 2) (tupleStacks 0) (by decide) a)

theorem saveCursor_eval (a : State 40 896) :
    Eval saveCursorCommand
      (5 * (a.stacks (tupleStacks 2)).length + 5 * (a.stacks (tupleStacks 7)).length + 10)
      a (saveCursorState a) := by
  have ht := Eval.seq (pushWord_eval (tupleStacks 2) (tupleStacks 0) (by decide) a)
    (pushWord_eval (tupleStacks 7) (tupleStacks 0) (by decide) _)
  have hw := pushWordState_outside (tupleStacks 2) (tupleStacks 0) (by decide) a
    (tupleStacks 7) (by decide) (by decide)
  change Eval saveCursorCommand _ a (saveCursorState a) at ht
  rw [hw] at ht
  convert ht using 1
  omega

theorem saveCursorState_words (a : State 40 896) :
    (saveCursorState a).stacks (tupleStacks 2) = [] ∧
      (saveCursorState a).stacks (tupleStacks 7) = [] ∧
      (saveCursorState a).stacks (tupleStacks 0) =
        Encoding.frame (a.stacks (tupleStacks 7)).reverse ++
          Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 0) := by
  constructor
  · unfold saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide), pushWordState_src]
  constructor
  · exact pushWordState_src _ _ _ _
  · unfold saveCursorState
    rw [pushWordState_dst, pushWordState_dst,
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact List.append_assoc _ _ _ |>.symm

def restoreCursorCommand : Cmd 40 896 :=
  .seq (popWordCommand (tupleStacks 0) (tupleStacks 7) (by decide))
    (popWordCommand (tupleStacks 0) (tupleStacks 2) (by decide))

noncomputable def restoreCursorState (a : State 40 896) (candidate remaining frames : List Bool) :
    State 40 896 :=
  popWordState (tupleStacks 0) (tupleStacks 2) (by decide)
    (popWordState (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
      (Encoding.frame candidate.reverse ++ frames)) candidate frames

theorem restoreCursor_eval (a : State 40 896) (candidate remaining frames : List Bool)
    (hs : a.stacks (tupleStacks 0) = Encoding.frame remaining.reverse ++
      Encoding.frame candidate.reverse ++ frames)
    (hc : a.stacks (tupleStacks 2) = []) (hr : a.stacks (tupleStacks 7) = []) :
    Eval restoreCursorCommand (6 * remaining.length + 6 * candidate.length + 8) a
      (restoreCursorState a candidate remaining frames) := by
  have hs' : a.stacks (tupleStacks 0) = Encoding.frame remaining.reverse ++
      (Encoding.frame candidate.reverse ++ frames) := by simpa only [List.append_assoc] using hs
  have h1 := popWord_eval (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
    (Encoding.frame candidate.reverse ++ frames) hs' hr
  have h2 := popWord_eval (tupleStacks 0) (tupleStacks 2) (by decide)
    (popWordState (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
      (Encoding.frame candidate.reverse ++ frames)) candidate frames
    (popWordState_src _ _ _ _ _ _) (by
      rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide)]
      exact hc)
  have ht := Eval.seq h1 h2
  change Eval restoreCursorCommand _ a (restoreCursorState a candidate remaining frames) at ht
  convert ht using 1
  omega

theorem restoreCursorState_words (a : State 40 896) (candidate remaining frames : List Bool) :
    (restoreCursorState a candidate remaining frames).stacks (tupleStacks 2) = candidate ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 7) = remaining ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 0) = frames := by
  constructor
  · exact popWordState_dst _ _ _ _ _ _
  constructor
  · unfold restoreCursorState
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide), popWordState_dst]
  · exact popWordState_src _ _ _ _ _ _

/-- Retain one emitted representative, with deepest head first on the physical
stack. The callback reconstructs its key from the exact retained assignment. -/
def recordRepresentativeCommand : Cmd 40 896 :=
  .seq (copyWord (tupleStacks 2) (tupleStacks 4) (tupleStacks 5))
    (pushWordCommand (tupleStacks 4) (tupleStacks 1) (by decide))

noncomputable def recordRepresentativeState (a : State 40 896) : State 40 896 :=
  pushWordState (tupleStacks 4) (tupleStacks 1) (by decide)
    (copyState (tupleStacks 2) (tupleStacks 4) a)

theorem recordRepresentative_eval (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval recordRepresentativeCommand (12 * (a.stacks (tupleStacks 2)).length + 10) a
      (recordRepresentativeState a) := by
  have hc := copyWord_eval (tupleStacks 2) (tupleStacks 4) (tupleStacks 5)
    (by decide) (by decide) (by decide) a ht
  have hh := Eval.seq hc (pushWord_eval (tupleStacks 4) (tupleStacks 1) (by decide) _)
  have hw : (copyState (tupleStacks 2) (tupleStacks 4) a).stacks (tupleStacks 4) =
      a.stacks (tupleStacks 2) := by simp [copyState, hp]
  change Eval recordRepresentativeCommand _ a (recordRepresentativeState a) at hh
  rw [hw] at hh
  convert hh using 1
  omega

theorem recordRepresentativeState_words (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) :
    (recordRepresentativeState a).stacks (tupleStacks 1) =
        Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 1) ∧
      (recordRepresentativeState a).stacks (tupleStacks 2) = a.stacks (tupleStacks 2) ∧
      (recordRepresentativeState a).stacks (tupleStacks 4) = [] := by
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_dst]
    simp [copyState, StackRoutines.copyStacks, hp]
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    simp [copyState, StackRoutines.copyStacks]
  · exact pushWordState_src _ _ _ _

/-- The remaining head count and physical color address are unary polynomial
words. They occupy two persistent ports, independent of the number of heads. -/
def descendLevelCommand : Cmd 40 896 :=
  .base (.seq (.atom (.pop (tupleStacks 6) 0 1))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push (tupleStacks 9) 0))
      (.seq (.atom (.peek (tupleStacks 6) 0 1))
        (.atom (.bnot controllerPorts.leaf 1))))))

def descendLevelState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.bnot controllerPorts.leaf 1).eval
    ((StructuredProgram.Atom.peek (tupleStacks 6) 0 1).eval
      ((StructuredProgram.Atom.push (tupleStacks 9) 0).eval
        ((StructuredProgram.Atom.set 0 true).eval
          ((StructuredProgram.Atom.pop (tupleStacks 6) 0 1).eval a))))

theorem descendLevel_eval (a : State 40 896) :
    Eval descendLevelCommand 5 a (descendLevelState a) :=
  .base (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))))

theorem descendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (ha : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendLevelState a).stacks (tupleStacks 6) = List.replicate remaining true ∧
      (descendLevelState a).stacks (tupleStacks 9) = List.replicate (address + 1) true ∧
      (descendLevelState a).regs controllerPorts.leaf = decide (remaining = 0) := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  cases remaining <;>
    simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

def ascendLevelCommand : Cmd 40 896 :=
  .base (.seq (.atom (.pop (tupleStacks 9) 0 1))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push (tupleStacks 6) 0))
      (.atom (.set controllerPorts.leaf false)))))

def ascendLevelState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.leaf false).eval
    ((StructuredProgram.Atom.push (tupleStacks 6) 0).eval
      ((StructuredProgram.Atom.set 0 true).eval
        ((StructuredProgram.Atom.pop (tupleStacks 9) 0 1).eval a)))

theorem ascendLevel_eval (a : State 40 896) :
    Eval ascendLevelCommand 4 a (ascendLevelState a) :=
  .base (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))))

theorem ascendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate remaining true)
    (ha : a.stacks (tupleStacks 9) = List.replicate (address + 1) true) :
    (ascendLevelState a).stacks (tupleStacks 6) = List.replicate (remaining + 1) true ∧
      (ascendLevelState a).stacks (tupleStacks 9) = List.replicate address true ∧
      (ascendLevelState a).regs controllerPorts.leaf = false := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

/-- Clear a current-head word before reusing its physical stack. -/
def clearWord (src : Fin 896) : Cmd 40 896 :=
  .call (StackRoutines.clearProgram src 0 1)

def clearState (src : Fin 896) (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

/-- The list specifies finitely many fixed physical ports in the control table;
it is never computed from or proportional to the assignment count. -/
def clearWords : List (Fin 896) → Cmd 40 896
  | [] => .base .skip
  | src :: rest => .seq (clearWord src) (clearWords rest)

def clearWordsState : List (Fin 896) → State 40 896 → State 40 896
  | [], a => a
  | src :: rest, a => clearWordsState rest (clearState src a)

def clearWordsTime : List (Fin 896) → State 40 896 → ℕ
  | [], _ => 0
  | src :: rest, a => 2 * (a.stacks src).length + 3 + clearWordsTime rest (clearState src a)

theorem clearWords_eval (ports : List (Fin 896)) (a : State 40 896) :
    Eval (clearWords ports) (clearWordsTime ports a) a (clearWordsState ports a) := by
  induction ports generalizing a with
  | nil => exact .base (.skip _)
  | cons src rest ih => exact .seq (clearWord_eval src a) (ih _)

theorem clearWordsState_stacks (ports : List (Fin 896)) (a : State 40 896)
    (i : Fin 896) :
    (clearWordsState ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  induction ports generalizing a with
  | nil => simp [clearWordsState]
  | cons src rest ih =>
    rw [clearWordsState, ih]
    by_cases hr : i ∈ rest
    · simp [hr]
    · by_cases hi : i = src
      · subst i
        simp [hr, clearState]
      · simp [hr, hi, clearState]

theorem clearWordsTime_le (ports : List (Fin 896)) (a : State 40 896) (width : ℕ)
    (hw : ∀ i, (a.stacks i).length ≤ width) :
    clearWordsTime ports a ≤ ports.length * (2 * width + 3) := by
  induction ports generalizing a with
  | nil => simp [clearWordsTime]
  | cons src rest ih =>
    have hs : ∀ i, ((clearState src a).stacks i).length ≤ width := by
      intro i
      by_cases hi : i = src
      · subst i; simp [clearState]
      · simpa [clearState, hi] using hw i
    have hh := ih (clearState src a) hs
    simp only [clearWordsTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    have := hw src
    omega

/-- These are the current generator's words. Suspended ancestors, emitted
representatives, remaining depth, and the physical head address are retained. -/
def currentHeadPorts : List (Fin 896) :=
  [tupleStacks 2, tupleStacks 3, tupleStacks 4, tupleStacks 5,
    tupleStacks 7, tupleStacks 8, tupleStacks 10, tupleStacks 11]

def leaveHeadCommand : Cmd 40 896 := clearWords currentHeadPorts

/-- Discard exactly one recorded representative after its subtree finishes. -/
def dropRepresentativeCommand : Cmd 40 896 :=
  .seq (popWordCommand (tupleStacks 1) (tupleStacks 4) (by decide))
    (clearWord (tupleStacks 4))

noncomputable def dropRepresentativeState (a : State 40 896) (word reps : List Bool) :
    State 40 896 :=
  clearState (tupleStacks 4)
    (popWordState (tupleStacks 1) (tupleStacks 4) (by decide) a word reps)

theorem dropRepresentative_eval (a : State 40 896) (word reps : List Bool)
    (hs : a.stacks (tupleStacks 1) = Encoding.frame word.reverse ++ reps)
    (he : a.stacks (tupleStacks 4) = []) :
    Eval dropRepresentativeCommand (8 * word.length + 7) a
      (dropRepresentativeState a word reps) := by
  have ht := Eval.seq (popWord_eval (tupleStacks 1) (tupleStacks 4) (by decide) a word reps hs he)
    (clearWord_eval (tupleStacks 4) _)
  rw [popWordState_dst] at ht
  change Eval dropRepresentativeCommand _ a (dropRepresentativeState a word reps) at ht
  convert ht using 1
  omega

theorem dropRepresentativeState_stacks (a : State 40 896) (word reps : List Bool) :
    (dropRepresentativeState a word reps).stacks (tupleStacks 1) = reps ∧
      (dropRepresentativeState a word reps).stacks (tupleStacks 4) = [] := by
  constructor
  · change Function.update
      (popWordState (tupleStacks 1) (tupleStacks 4) (by decide) a word reps).stacks
      (tupleStacks 4) [] (tupleStacks 1) = reps
    rw [Function.update_of_ne (by decide : tupleStacks 1 ≠ tupleStacks 4)]
    exact popWordState_src _ _ _ _ _ _
  · simp [dropRepresentativeState, clearState]

/-- Root detection uses the presence bit of the frame stack; a zero-bit or
empty payload frame is still present because it has an encoded delimiter. -/
def testParentCommand : Cmd 40 896 :=
  .base (.atom (.peek (tupleStacks 0) 0 controllerPorts.active))

def testParentState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.peek (tupleStacks 0) 0 controllerPorts.active).eval a

theorem testParent_eval (a : State 40 896) :
    Eval testParentCommand 1 a (testParentState a) := .base (.atom _ _)

theorem testParentState_flag (a : State 40 896) :
    (testParentState a).regs controllerPorts.active =
      decide (a.stacks (tupleStacks 0) ≠ []) := by
  cases hs : a.stacks (tupleStacks 0) <;>
    simp [testParentState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hs]

/-- Exact full-word test used before the candidate predicate is invoked. -/
def testAvailableCommand : Cmd 40 896 :=
  .seq (CounterForPrograms.testCmd remainingPorts)
    (.base (.atom (.copy controllerPorts.available (remainingPorts.register 2))))

noncomputable def testAvailableState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.copy controllerPorts.available (remainingPorts.register 2)).eval
    (CounterForPrograms.testResult remainingPorts a)

theorem testAvailable_eval (a : State 40 896) (hs : a.stacks remainingPorts.scratch = []) :
    Eval testAvailableCommand (8 * (a.stacks remainingPorts.counter).length + 8) a
      (testAvailableState a) := by
  have ht := Eval.seq (CounterForPrograms.test_eval remainingPorts a hs)
    (Eval.base (StructuredProgram.Eval.atom
      (.copy controllerPorts.available (remainingPorts.register 2)) _))
  simpa only [testAvailableCommand, testAvailableState, Nat.add_assoc] using ht

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

/-- Every nonterminal cursor is exactly the fixed-width word consumed by the
attained-signature predicate, not merely a short encoding of the same value. -/
theorem advanceState_assignment (a : State 40 896) (h : ℕ) (candidate : Fin (2 ^ h))
    (hc : a.stacks candidatePorts.counter = ExecCNFTupleEnumeration.fixedBits h candidate)
    (hn : candidate.val + 1 < 2 ^ h) :
    (advanceState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits h (candidate.val + 1) := by
  rw [advanceState_candidate, hc]
  exact Counters.increment_word candidate hn

theorem advanceState_remaining_value (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = [])
    (hp : 0 < CounterPrograms.value (a.stacks remainingPorts.counter)) :
    CounterPrograms.value ((advanceState a).stacks remainingPorts.counter) =
      CounterPrograms.value (a.stacks remainingPorts.counter) - 1 := by
  rw [advanceState_remaining a hs]
  have hv := CounterPrograms.value_decrement hp
  omega

theorem resetState_assignment (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits h 0 := by
  rw [(resetState_words a h hw hc hp).1]
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])

/-- A current-head reset initializes the predecessor cursor to the same
fixed-width zero word, preserving the freshly initialized candidate and fuel. -/
def resetGeneratorCommand : Cmd 40 896 :=
  .seq resetCommand (copyWord 651 (tupleStacks 8) (tupleStacks 5))

noncomputable def resetGeneratorState (a : State 40 896) : State 40 896 :=
  copyState 651 (tupleStacks 8) (resetState a)

theorem resetState_source (a : State 40 896) :
    (resetState a).stacks 651 = a.stacks 651 := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  change (initialFuelState c).stacks 651 = a.stacks 651
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _ 651
    (by decide) (by decide)]
  simp [c, b, copyState, StackRoutines.copyStacks,
    (by decide : (651 : Fin 896) ≠ tupleStacks 2),
    (by decide : (651 : Fin 896) ≠ tupleStacks 4)]

theorem resetState_scratch (a : State 40 896) :
    (resetState a).stacks (tupleStacks 5) = a.stacks (tupleStacks 5) := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  change (initialFuelState c).stacks (tupleStacks 5) = a.stacks (tupleStacks 5)
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _
    (tupleStacks 5) (by decide) (by decide)]
  simp [c, b, copyState, StackRoutines.copyStacks]

theorem resetGenerator_eval (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (he : a.stacks (tupleStacks 7) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    Eval resetGeneratorCommand (25 * h + 22) a (resetGeneratorState a) := by
  have hr := reset_eval a h hw he ht hp
  have hh := copyWord_eval 651 (tupleStacks 8) (tupleStacks 5)
    (by decide) (by decide) (by decide) (resetState a) ((resetState_scratch a).trans ht)
  have hall := Eval.seq hr hh
  rw [resetState_source, hw, List.length_replicate] at hall
  change Eval resetGeneratorCommand _ a (resetGeneratorState a) at hall
  convert hall using 1
  omega

/-- Generic frame operations preserve every controller flag. -/
theorem pushWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (pushWordState src dst h a).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

theorem popWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (popWordState src dst h a word tail).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

theorem clearWordsState_register_frame (ports : List (Fin 896))
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (clearWordsState ports a).regs i = a.regs i := by
  induction ports generalizing a with
  | nil => rfl
  | cons src rest ih =>
    rw [clearWordsState, ih]
    exact StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
