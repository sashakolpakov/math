import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecWorklistProgram
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyMeasured

namespace OAI.Algorithms

/-!
# An actual pending-list loop around a finite splitter program

The supplied splitter is a fixed finite instruction table. Its correctness
premise is an actual trace contract restricted to an invariant P on the current
formula; no cost or behavior is assumed on arbitrary unbounded machine states.
All pending and output suffixes are retained. The outer loop itself inspects the
encoded list tag, invokes the two finite programs, and repeats.
-/

namespace SubexponentialSAT.ExecWorklistLoop

open BitProgram StructuredCalls

variable {α : Type*}

abbrev canonicalData (enc : α → List Bool) (s : ExecSparsifyWorklist.State α) : ExecWorklistProgram.Data :=
  ExecWorklistProgram.data false false false false (Encoding.encodeList enc s.pending)
    (Encoding.encodeList enc s.leaves) [] []

abbrev loopData (enc : α → List Bool) (s : ExecSparsifyWorklist.State α) : ExecWorklistProgram.Data :=
  ExecWorklistProgram.data false false true (!s.pending.isEmpty) (Encoding.encodeList enc s.pending)
    (Encoding.encodeList enc s.leaves) [] []

abbrev updatedData (enc : α → List Bool) (terminal found : Bool) (s : ExecSparsifyWorklist.State α) : ExecWorklistProgram.Data :=
  ExecWorklistProgram.data terminal false false found (Encoding.encodeList enc s.pending)
    (Encoding.encodeList enc s.leaves) [] []

abbrev splitData (enc : α → List Bool) (x : α) (pending leaves : List α)
    (result : Option (α × α)) : ExecWorklistProgram.Data :=
  match result with
  | none => ExecWorklistProgram.data true false false false (Encoding.encodeList enc (x :: pending))
      (Encoding.encodeList enc leaves) [] []
  | some (a,b) => ExecWorklistProgram.data false false false false (Encoding.encodeList enc (x :: pending))
      (Encoding.encodeList enc leaves) (ExecWorklistProgram.record (enc a)) (ExecWorklistProgram.record (enc b))

/-- This is a local, actual finite-program trace, not a semantic runtime oracle.
P can include reachability from one initial CNF as well as its width invariant. -/
abbrev RealizesOn {labels : ℕ} (splitter : Program 4 5 labels) (enc : α → List Bool)
    (split : α → Option (α × α)) (P : α → Prop) (cost : α → ℕ) : Prop :=
  ∀ x, P x → ∀ pending leaves,
    Trace splitter (cost x)
      ((loopData enc ⟨x :: pending, leaves, 0⟩).withPC (some splitter.entry))
      ((splitData enc x pending leaves (split x)).withPC none)

abbrev peekPending : Cmd 4 5 := .base (.atom (.peek 0 3 1))
abbrev clearDecision : Cmd 4 5 := .base (.atom (.set 2 false))
abbrev clearPresent : Cmd 4 5 := .base (.atom (.set 1 false))
abbrev resetAndPeek : Cmd 4 5 := .seq clearDecision peekPending

abbrev body {labels : ℕ} (splitter : Program 4 5 labels) : Cmd 4 5 :=
  .seq (.call splitter) (.seq (.call ExecWorklistProgram.program) resetAndPeek)

abbrev command {labels : ℕ} (splitter : Program 4 5 labels) : Cmd 4 5 :=
  .seq peekPending (.seq (.while 3 (body splitter)) clearPresent)

/-- The generated control is fixed by the finite splitter table alone. -/
abbrev program {labels : ℕ} (splitter : Program 4 5 labels) :
    Program 4 5 (StructuredCalls.size (command splitter) + 1) :=
  compiled (command splitter) 0 1

theorem program_label_count {labels : ℕ} (splitter : Program 4 5 labels) :
    StructuredCalls.size (command splitter) + 1 = labels + 67 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]
  omega

private theorem data_ext (a b : ExecWorklistProgram.Data) (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

private theorem clearDecision_value (enc : α → List Bool) (terminal found : Bool) (s : ExecSparsifyWorklist.State α) :
    (StructuredProgram.Atom.set 2 false).eval (updatedData enc terminal found s) =
      updatedData enc false found s := by
  apply data_ext <;> funext i <;> fin_cases i <;>
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

private theorem peek_value (enc : α → List Bool) (found : Bool) (s : ExecSparsifyWorklist.State α) :
    (StructuredProgram.Atom.peek 0 3 1).eval (updatedData enc false found s) = loopData enc s := by
  cases hp : s.pending with
  | nil =>
    apply data_ext <;> funext i <;> fin_cases i <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs, hp, Encoding.encodeList]
  | cons x xs =>
    apply data_ext <;> funext i <;> fin_cases i <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs, hp, Encoding.encodeList]

theorem resetAndPeek_eval (enc : α → List Bool) (terminal found : Bool) (s : ExecSparsifyWorklist.State α) :
    Eval resetAndPeek 2 (updatedData enc terminal found s) (loopData enc s) := by
  have hc : Eval clearDecision 1 (updatedData enc terminal found s) (updatedData enc false found s) := by
    simpa only [clearDecision, clearDecision_value] using
      Eval.base (StructuredProgram.Eval.atom (.set 2 false) (updatedData enc terminal found s))
  have hp : Eval peekPending 1 (updatedData enc false found s) (loopData enc s) := by
    simpa only [peekPending, peek_value] using
      Eval.base (StructuredProgram.Eval.atom (.peek 0 3 1) (updatedData enc false found s))
  exact .seq hc hp

theorem initialPeek_eval (enc : α → List Bool) (s : ExecSparsifyWorklist.State α) :
    Eval peekPending 1 (canonicalData enc s) (loopData enc s) := by
  simpa only [peekPending, peek_value] using
    Eval.base (StructuredProgram.Eval.atom (.peek 0 3 1) (updatedData enc false false s))

theorem clearPresent_eval (enc : α → List Bool) (s : ExecSparsifyWorklist.State α) (h : s.pending = []) :
    Eval clearPresent 1 (loopData enc s) (canonicalData enc s) := by
  have he : (StructuredProgram.Atom.set 1 false).eval (loopData enc s) = canonicalData enc s := by
    apply data_ext <;> funext i <;> fin_cases i <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, h]
  simpa only [clearPresent, he] using
    Eval.base (StructuredProgram.Eval.atom (.set 1 false) (loopData enc s))

/-- Exact local work of the already-proved encoded record update. -/
abbrev updateCost (enc : α → List Bool) (x : α) : Option (α × α) → ℕ
  | none => 13 * (enc x).length + 20
  | some (a,b) => 5 * (enc x).length + 13 * (enc b).length + 13 * (enc a).length + 46

theorem body_eval {labels : ℕ} (splitter : Program 4 5 labels) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter enc branch.split P cost)
    (x : α) (hx : P x) (pending leaves : List α) (visits : ℕ) :
    Eval (body splitter) (cost x + updateCost enc x (branch.split x) + 2)
      (loopData enc ⟨x :: pending, leaves, visits⟩)
      (loopData enc (ExecSparsifyWorklist.step branch.split ⟨x :: pending, leaves, visits⟩)) := by
  have hs := hreal x hx pending leaves
  cases he : branch.split x with
  | none =>
    have hc : Eval (.call splitter) (cost x)
        (loopData enc ⟨x :: pending, leaves, visits⟩)
        (splitData enc x pending leaves none) := by
      apply Eval.call
      simpa only [he] using hs
    have hu : Eval (.call ExecWorklistProgram.program) (updateCost enc x none)
        (splitData enc x pending leaves none)
        (updatedData enc true false ⟨pending, x :: leaves, visits + 1⟩) := by
      apply Eval.call
      simpa [splitData, updatedData, updateCost, List.append_nil] using
        ExecWorklistProgram.terminal_list_trace enc x pending leaves [] [] [] [] false false false
    have hp := resetAndPeek_eval enc true false (ExecSparsifyWorklist.State.mk pending (x :: leaves) (visits + 1))
    have ht := Eval.seq hc (Eval.seq hu hp)
    simpa only [body, ExecSparsifyWorklist.step, he, Nat.add_assoc] using ht
  | some pair =>
    rcases pair with ⟨a,b⟩
    have hc : Eval (.call splitter) (cost x)
        (loopData enc ⟨x :: pending, leaves, visits⟩)
        (splitData enc x pending leaves (some (a,b))) := by
      apply Eval.call
      simpa only [he] using hs
    have hu : Eval (.call ExecWorklistProgram.program) (updateCost enc x (some (a,b)))
        (splitData enc x pending leaves (some (a,b)))
        (updatedData enc false true ⟨a :: b :: pending, leaves, visits + 1⟩) := by
      apply Eval.call
      simpa [splitData, updatedData, updateCost, List.append_nil] using
        ExecWorklistProgram.branch_list_trace enc x a b pending [] (Encoding.encodeList enc leaves) [] [] false false false
    have hp := resetAndPeek_eval enc false true (ExecSparsifyWorklist.State.mk (a :: b :: pending) leaves (visits + 1))
    have ht := Eval.seq hc (Eval.seq hu hp)
    simpa only [body, ExecSparsifyWorklist.step, he, Nat.add_assoc] using ht

/-- Exact work along the specification tree: local split, encoded update, and
three loop instructions per visited node. This tree is used only in proofs. -/
def nodeWork (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (x : α) : ℕ :=
  let localWork := cost x + updateCost enc x (branch.split x) + 3
  match _h : branch.split x with
  | none => localWork
  | some (a,b) => localWork + nodeWork enc branch cost a + nodeWork enc branch cost b
termination_by branch.mass x
decreasing_by
  · exact (branch.decreases x a b _h).1
  · exact (branch.decreases x a b _h).2

theorem nodeWork_none (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (x : α) (h : branch.split x = none) :
    nodeWork enc branch cost x = cost x + updateCost enc x none + 3 := by
  rw [nodeWork, h]

theorem nodeWork_some (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (x a b : α) (h : branch.split x = some (a,b)) :
    nodeWork enc branch cost x = cost x + updateCost enc x (some (a,b)) + 3 +
      nodeWork enc branch cost a + nodeWork enc branch cost b := by
  rw [nodeWork, h]

def forestWork (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (pending : List α) : ℕ := (pending.map (nodeWork enc branch cost)).sum

@[simp] theorem forestWork_nil (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) : forestWork enc branch cost [] = 0 := rfl

@[simp] theorem forestWork_cons (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (x : α) (xs : List α) :
    forestWork enc branch cost (x :: xs) = nodeWork enc branch cost x + forestWork enc branch cost xs := rfl

theorem forestWork_step (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (cost : α → ℕ) (x : α) (pending leaves : List α) (visits : ℕ) :
    forestWork enc branch cost (x :: pending) = cost x + updateCost enc x (branch.split x) + 3 +
      forestWork enc branch cost
        (ExecSparsifyWorklist.step branch.split ⟨x :: pending, leaves, visits⟩).pending := by
  cases h : branch.split x with
  | none =>
    simp only [ExecSparsifyWorklist.step, h, forestWork_cons, nodeWork_none enc branch cost x h]
  | some pair =>
    rcases pair with ⟨a,b⟩
    simp only [ExecSparsifyWorklist.step, h, forestWork_cons, nodeWork_some enc branch cost x a b h]
    omega

/-- The loop is proved only along states satisfying P; its recursive calls use
the actual syntactic child-closure proof. No specification on other states is needed. -/
theorem while_eval {labels : ℕ} (splitter : Program 4 5 labels) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (s : ExecSparsifyWorklist.State α) (hs : ExecSparsifyWorklist.Invariant P s) :
    Eval (.while 3 (body splitter)) (forestWork enc branch cost s.pending + 1)
      (loopData enc s) (loopData enc (ExecSparsifyWorklist.run branch s)) := by
  induction s using (measure (fun s : ExecSparsifyWorklist.State α =>
      ExecSparsifyWorklist.potential branch.mass s.pending)).wf.induction with
  | h s ih =>
    rcases s with ⟨pending,leaves,visits⟩
    cases pending with
    | nil =>
      have hr : ExecSparsifyWorklist.run branch ⟨[],leaves,visits⟩ = ⟨[],leaves,visits⟩ := rfl
      rw [hr]
      exact .while_false rfl
    | cons x xs =>
      let s : ExecSparsifyWorklist.State α := ⟨x :: xs, leaves, visits⟩
      have hn : s.pending ≠ [] := by simp [s]
      have hd := ExecSparsifyWorklist.step_potential_lt branch s hn
      have hnext := ExecSparsifyWorklist.step_invariant branch.split P hclosed s hs
      have hr := ih (ExecSparsifyWorklist.step branch.split s) hd hnext
      have hx : P x := hs.1 x List.mem_cons_self
      have hb := body_eval splitter enc branch P cost hreal x hx xs leaves visits
      have ht := Eval.while_true (test := (3 : Fin 4)) (by rfl) hb hr
      have he := ExecSparsifyWorklist.run_after_step branch s hn
      have hw := forestWork_step enc branch cost x xs leaves visits
      rw [← he] at ht
      dsimp only [s] at ht
      convert ht using 1
      change forestWork enc branch cost (x :: xs) + 1 =
        (cost x + updateCost enc x (branch.split x) + 2) +
          (forestWork enc branch cost
            (ExecSparsifyWorklist.step branch.split ⟨x :: xs, leaves, visits⟩).pending + 1) + 1
      rw [hw]
      omega

/-- Complete finite-table execution of the outer loop, with its exact cumulative
cost and exactly the leaves produced by the existing verified traversal. -/
theorem run_trace {labels : ℕ} (splitter : Program 4 5 labels) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (s : ExecSparsifyWorklist.State α) (hs : ExecSparsifyWorklist.Invariant P s) :
    Trace (program splitter) (forestWork enc branch cost s.pending + 4)
      ((canonicalData enc s).withPC (some (program splitter).entry))
      ((canonicalData enc (ExecSparsifyWorklist.run branch s)).withPC none) := by
  have hp := initialPeek_eval enc s
  have hw := while_eval splitter enc branch P cost hreal hclosed s hs
  have hc := clearPresent_eval enc (ExecSparsifyWorklist.run branch s)
    (ExecSparsifyWorklist.run_pending_nil branch s)
  have he : Eval (command splitter) (1 + ((forestWork enc branch cost s.pending + 1) + 1))
      (canonicalData enc s) (canonicalData enc (ExecSparsifyWorklist.run branch s)) :=
    .seq hp (.seq hw hc)
  have ht := compiled_halt_trace he 0 1
  convert ht using 1
  omega

/-- The bound is restricted to the same invariant as the real splitter contract. -/
theorem nodeWork_le_visits (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (bound : ℕ)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hbound : ∀ x, P x → cost x + updateCost enc x (branch.split x) ≤ bound)
    (x : α) (hx : P x) :
    nodeWork enc branch cost x ≤ (bound + 3) * (ExecSparsifyWorklist.tree branch x).nodeCount := by
  induction x using (measure branch.mass).wf.induction with
  | h x ih =>
    have hc := hbound x hx
    cases he : branch.split x with
    | none =>
      rw [nodeWork_none enc branch cost x he, ExecSparsifyWorklist.tree_none branch x he]
      simp only [BranchTree.Tree.nodeCount, Nat.mul_one]
      simpa only [he] using Nat.add_le_add_right hc 3
    | some pair =>
      rcases pair with ⟨a,b⟩
      have hd := branch.decreases x a b he
      have hab := hclosed x a b hx he
      have ha := ih a hd.1 hab.1
      have hb := ih b hd.2 hab.2
      rw [nodeWork_some enc branch cost x a b he, ExecSparsifyWorklist.tree_some branch x a b he]
      simp only [BranchTree.Tree.nodeCount]
      rw [he] at hc
      calc
        _ ≤ bound + 3 + (bound + 3) * (ExecSparsifyWorklist.tree branch a).nodeCount +
            (bound + 3) * (ExecSparsifyWorklist.tree branch b).nodeCount := by omega
        _ = _ := by ring

/-- Primitive-machine execution starting from one encoded pending formula. -/
theorem initial_run_primitive {labels : ℕ} (splitter : Program 4 5 labels) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ) (bound : ℕ)
    (hreal : RealizesOn splitter enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hbound : ∀ x, P x → cost x + updateCost enc x (branch.split x) ≤ bound)
    (x : α) (hx : P x) :
    Computation.RunsIn (BitProgram.primitive (program splitter)).step
      (BitProgram.primitiveOverhead (program splitter) *
        ((bound + 3) * (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits + 4))
      (BitProgram.primitiveCfg (program splitter)
        ((canonicalData enc (ExecSparsifyWorklist.initial x)).withPC (some (program splitter).entry)))
      (BitProgram.primitiveCfg (program splitter)
        ((canonicalData enc (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x))).withPC none)) := by
  have hi : ExecSparsifyWorklist.Invariant P (ExecSparsifyWorklist.initial x) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using hx
  have ht := BitProgram.primitive_trace (program splitter)
    (run_trace splitter enc branch P cost hreal hclosed (ExecSparsifyWorklist.initial x) hi)
  apply ht.mono
  apply Nat.mul_le_mul_left
  rw [ExecSparsifyWorklist.initial_run_visits]
  simpa [ExecSparsifyWorklist.initial] using
    Nat.add_le_add_right (nodeWork_le_visits enc branch P cost bound hclosed hbound x hx) 4

/-- The fixed small tail performs the encoded update and refreshes the guard. -/
abbrev nodeTail : Cmd 4 5 := .seq (.call ExecWorklistProgram.program) resetAndPeek

theorem nodeTail_eval (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (x : α) (pending leaves : List α) (visits : ℕ) :
    Eval nodeTail (updateCost enc x (branch.split x) + 2)
      (splitData enc x pending leaves (branch.split x))
      (loopData enc (ExecSparsifyWorklist.step branch.split ⟨x :: pending, leaves, visits⟩)) := by
  cases he : branch.split x with
  | none =>
    have hu : Eval (.call ExecWorklistProgram.program) (updateCost enc x none)
        (splitData enc x pending leaves none)
        (updatedData enc true false ⟨pending, x :: leaves, visits + 1⟩) := by
      apply Eval.call
      simpa [splitData, updatedData, updateCost, List.append_nil] using
        ExecWorklistProgram.terminal_list_trace enc x pending leaves [] [] [] [] false false false
    have hp := resetAndPeek_eval enc true false (ExecSparsifyWorklist.State.mk pending (x :: leaves) (visits + 1))
    simpa only [nodeTail, ExecSparsifyWorklist.step, he] using Eval.seq hu hp
  | some pair =>
    rcases pair with ⟨a,b⟩
    have hu : Eval (.call ExecWorklistProgram.program) (updateCost enc x (some (a,b)))
        (splitData enc x pending leaves (some (a,b)))
        (updatedData enc false true ⟨a :: b :: pending, leaves, visits + 1⟩) := by
      apply Eval.call
      simpa [splitData, updatedData, updateCost, List.append_nil] using
        ExecWorklistProgram.branch_list_trace enc x a b pending [] (Encoding.encodeList enc leaves) [] [] false false false
    have hp := resetAndPeek_eval enc false true (ExecSparsifyWorklist.State.mk (a :: b :: pending) leaves (visits + 1))
    simpa only [nodeTail, ExecSparsifyWorklist.step, he] using Eval.seq hu hp

namespace Ambient

variable {r s : ℕ}

/-- Specification embedding only; runtime uses the finite lifted instruction tables. -/
noncomputable def liftData (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s)
    (frame : StructuredProgram.State r s) (d : ExecWorklistProgram.Data) : StructuredProgram.State r s :=
  embedState register stack frame d

/-- Compile and call one fixed small helper in the larger splitter environment. -/
abbrev liftCommand (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s)
    (c : Cmd 4 5) : Cmd r s :=
  .call (ProgramLinking.liftProgram (compiled c 0 1) register stack)

@[simp] theorem liftCommand_size (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s)
    (c : Cmd 4 5) : StructuredCalls.size (liftCommand register stack c) = StructuredCalls.size c + 1 := rfl

theorem liftCommand_eval (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s)
    (frame : StructuredProgram.State r s) (hr : Function.Injective register) (hs : Function.Injective stack)
    {c : Cmd 4 5} {n : ℕ} {a b : ExecWorklistProgram.Data} (h : Eval c n a b) :
    Eval (liftCommand register stack c) (n + 1)
      (liftData register stack frame a) (liftData register stack frame b) :=
  eval_call_lifted (compiled c 0 1) register stack frame hr hs (compiled_halt_trace h 0 1)

/-- Actual splitter correctness is required only on P. The frame may contain
persistent thresholds or additional empty scratch ports; it is restored at return. -/
abbrev RealizesOn {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (enc : α → List Bool) (split : α → Option (α × α)) (P : α → Prop) (cost : α → ℕ) : Prop :=
  ∀ x, P x → ∀ pending leaves,
    Trace splitter (cost x)
      ((liftData register stack frame (loopData enc ⟨x :: pending, leaves, 0⟩)).withPC (some splitter.entry))
      ((liftData register stack frame (splitData enc x pending leaves (split x))).withPC none)

abbrev body {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) : Cmd r s :=
  .seq (.call splitter) (liftCommand register stack nodeTail)

abbrev command {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) : Cmd r s :=
  .seq (liftCommand register stack peekPending)
    (.seq (.while (register 3) (body splitter register stack)) (liftCommand register stack clearPresent))

/-- No ambient size, port map, or control label depends on the data. -/
abbrev program {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) :
    Program r s (StructuredCalls.size (command splitter register stack) + 1) :=
  compiled (command splitter register stack) (stack 0) (stack 1)

theorem program_label_count {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) :
    StructuredCalls.size (command splitter register stack) + 1 = labels + 70 := by
  simp [ StructuredCalls.size, StructuredProgram.size]
  omega

theorem body_eval {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter register stack frame enc branch.split P cost)
    (x : α) (hx : P x) (pending leaves : List α) (visits : ℕ) :
    Eval (body splitter register stack) (cost x + updateCost enc x (branch.split x) + 3)
      (liftData register stack frame (loopData enc ⟨x :: pending, leaves, visits⟩))
      (liftData register stack frame
        (loopData enc (ExecSparsifyWorklist.step branch.split ⟨x :: pending, leaves, visits⟩))) := by
  have hsplit : Eval (.call splitter) (cost x)
      (liftData register stack frame (loopData enc ⟨x :: pending, leaves, visits⟩))
      (liftData register stack frame (splitData enc x pending leaves (branch.split x))) :=
    .call splitter (hreal x hx pending leaves)
  have htail := liftCommand_eval register stack frame hr hs (nodeTail_eval enc branch x pending leaves visits)
  simpa only [body, Nat.add_assoc] using Eval.seq hsplit htail

/-- The only loop guard is the current encoded pending-list tag. -/
theorem while_eval {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter register stack frame enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (state : ExecSparsifyWorklist.State α) (hstate : ExecSparsifyWorklist.Invariant P state) :
    Eval (.while (register 3) (body splitter register stack))
      (forestWork enc branch (fun x => cost x + 1) state.pending + 1)
      (liftData register stack frame (loopData enc state))
      (liftData register stack frame (loopData enc (ExecSparsifyWorklist.run branch state))) := by
  induction state using (measure (fun state : ExecSparsifyWorklist.State α =>
      ExecSparsifyWorklist.potential branch.mass state.pending)).wf.induction with
  | h state ih =>
    rcases state with ⟨pending,leaves,visits⟩
    cases pending with
    | nil =>
      have hrun : ExecSparsifyWorklist.run branch ⟨[],leaves,visits⟩ = ⟨[],leaves,visits⟩ := rfl
      rw [hrun]
      apply Eval.while_false
      exact (embedState_register register stack frame _ hr 3).trans rfl
    | cons x xs =>
      let state : ExecSparsifyWorklist.State α := ⟨x :: xs, leaves, visits⟩
      have hn : state.pending ≠ [] := by simp [state]
      have hd := ExecSparsifyWorklist.step_potential_lt branch state hn
      have hnext := ExecSparsifyWorklist.step_invariant branch.split P hclosed state hstate
      have hrec := ih (ExecSparsifyWorklist.step branch.split state) hd hnext
      have hx : P x := hstate.1 x List.mem_cons_self
      have hb := body_eval splitter register stack frame hr hs enc branch P cost hreal x hx xs leaves visits
      have hguard : (liftData register stack frame (loopData enc state)).regs (register 3) = true :=
        (embedState_register register stack frame _ hr 3).trans rfl
      have ht := Eval.while_true hguard hb hrec
      have he := ExecSparsifyWorklist.run_after_step branch state hn
      have hw := forestWork_step enc branch (fun x => cost x + 1) x xs leaves visits
      rw [← he] at ht
      dsimp only [state] at ht
      convert ht using 1
      change forestWork enc branch (fun x => cost x + 1) (x :: xs) + 1 =
        (cost x + updateCost enc x (branch.split x) + 3) +
          (forestWork enc branch (fun x => cost x + 1)
            (ExecSparsifyWorklist.step branch.split ⟨x :: xs, leaves, visits⟩).pending + 1) + 1
      rw [hw]
      omega

/-- Exact cumulative finite-table trace in the splitter's real ambient machine. -/
theorem run_trace {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : RealizesOn splitter register stack frame enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (state : ExecSparsifyWorklist.State α) (hstate : ExecSparsifyWorklist.Invariant P state) :
    Trace (program splitter register stack)
      (forestWork enc branch (fun x => cost x + 1) state.pending + 6)
      ((liftData register stack frame (canonicalData enc state)).withPC (some (program splitter register stack).entry))
      ((liftData register stack frame (canonicalData enc (ExecSparsifyWorklist.run branch state))).withPC none) := by
  have hp := liftCommand_eval register stack frame hr hs (initialPeek_eval enc state)
  have hw := while_eval splitter register stack frame hr hs enc branch P cost hreal hclosed state hstate
  have hc := liftCommand_eval register stack frame hr hs
    (clearPresent_eval enc (ExecSparsifyWorklist.run branch state) (ExecSparsifyWorklist.run_pending_nil branch state))
  have he : Eval (command splitter register stack)
      (2 + ((forestWork enc branch (fun x => cost x + 1) state.pending + 1) + 2))
      (liftData register stack frame (canonicalData enc state))
      (liftData register stack frame (canonicalData enc (ExecSparsifyWorklist.run branch state))) :=
    .seq hp (.seq hw hc)
  have ht := compiled_halt_trace he (stack 0) (stack 1)
  convert ht using 1
  omega

/-- Primitive runtime uses the local bound only on P, hence it can be supplied
solely for reachable bounded CNFs. Accumulated output length is never charged. -/
theorem initial_run_primitive {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop)
    (cost : α → ℕ) (bound : ℕ)
    (hreal : RealizesOn splitter register stack frame enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hbound : ∀ x, P x → cost x + updateCost enc x (branch.split x) ≤ bound)
    (x : α) (hx : P x) :
    Computation.RunsIn (BitProgram.primitive (program splitter register stack)).step
      (BitProgram.primitiveOverhead (program splitter register stack) *
        ((bound + 4) * (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits + 6))
      (BitProgram.primitiveCfg (program splitter register stack)
        ((liftData register stack frame (canonicalData enc (ExecSparsifyWorklist.initial x))).withPC
          (some (program splitter register stack).entry)))
      (BitProgram.primitiveCfg (program splitter register stack)
        ((liftData register stack frame
          (canonicalData enc (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)))).withPC none)) := by
  have hi : ExecSparsifyWorklist.Invariant P (ExecSparsifyWorklist.initial x) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using hx
  have ht := BitProgram.primitive_trace (program splitter register stack)
    (run_trace splitter register stack frame hr hs enc branch P cost hreal hclosed (ExecSparsifyWorklist.initial x) hi)
  apply ht.mono
  apply Nat.mul_le_mul_left
  rw [ExecSparsifyWorklist.initial_run_visits]
  have hb : ∀ y, P y → (cost y + 1) + updateCost enc y (branch.split y) ≤ bound + 1 := by
    intro y hy
    have := hbound y hy
    omega
  have hnode := nodeWork_le_visits enc branch P (fun y => cost y + 1) (bound + 1) hclosed hb x hx
  simpa [ExecSparsifyWorklist.initial, Nat.add_assoc] using Nat.add_le_add_right hnode 6

end Ambient

/-- Only formulas generated from this input by the actual deterministic split. -/
inductive Reachable (split : α → Option (α × α)) (start : α) : α → Prop
  | root : Reachable split start start
  | left {x a b} : Reachable split start x → split x = some (a,b) → Reachable split start a
  | right {x a b} : Reachable split start x → split x = some (a,b) → Reachable split start b

theorem reachable_closed (split : α → Option (α × α)) (start : α) :
    ExecSparsifyWorklist.SplitClosed split (Reachable split start) := by
  intro x a b hx h
  exact ⟨Reachable.left hx h, Reachable.right hx h⟩

theorem reachable_and_closed (split : α → Option (α × α)) (start : α) (P : α → Prop)
    (hP : ExecSparsifyWorklist.SplitClosed split P) :
    ExecSparsifyWorklist.SplitClosed split (fun x => Reachable split start x ∧ P x) := by
  intro x a b hx h
  have hp := hP x a b hx.2 h
  exact ⟨⟨Reachable.left hx.1 h,hp.1⟩,⟨Reachable.right hx.1 h,hp.2⟩⟩

section ConcreteExecution

variable {n r s labels : ℕ}

/-- The contract domain for one actual sparsification run. Width and represented
clause distinctness are proved along the run; arbitrary machine states are excluded. -/
def ExecutionInvariant (z : ℕ → ℕ) (k : ℕ) (F : ExecSparsifyWorklist.Formula n)
    (G : ExecSparsifyWorklist.Formula n) : Prop :=
  Reachable (ExecSparsifyWorklist.splitFormula z k) (ExecSparsifyWorklist.normalizedInput F) G ∧
    ExecSparsifyWorklist.BoundedNode k G

theorem executionInvariant_closed (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : ExecSparsifyWorklist.Formula n) :
    ExecSparsifyWorklist.SplitClosed (ExecSparsifyWorklist.executableBranching z k hz).split
      (ExecutionInvariant z k F) :=
  reachable_and_closed _ _ _ (ExecSparsifyWorklist.boundedNode_closed z k hz)

theorem executionInvariant_initial (z : ℕ → ℕ) (k : ℕ) (F : ExecSparsifyWorklist.Formula n)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) :
    ExecutionInvariant z k F (ExecSparsifyWorklist.normalizedInput F) :=
  ⟨Reachable.root, ExecSparsifyWorklist.normalizedInput_boundedNode F k hF⟩

/-- The actual finite outer program returns exactly the measured executor's
state. Only its supplied splitter's reachable, bounded trace contract is assumed. -/
theorem executeM_trace (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : ExecSparsifyWorklist.Formula n → List Bool) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : ExecSparsifyWorklist.Formula n)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) (cost : ExecSparsifyWorklist.Formula n → ℕ)
    (hreal : Ambient.RealizesOn splitter register stack frame enc
      (ExecSparsifyWorklist.splitFormula z k) (ExecutionInvariant z k F) cost) :
    Trace (Ambient.program splitter register stack)
      (nodeWork enc (ExecSparsifyWorklist.executableBranching z k hz) (fun x => cost x + 1)
        (ExecSparsifyWorklist.normalizedInput F) + 6)
      ((Ambient.liftData register stack frame (canonicalData enc
        (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F)))).withPC
          (some (Ambient.program splitter register stack).entry))
      ((Ambient.liftData register stack frame
        (canonicalData enc (ExecSparsifyWorklist.executeM z k hz F).1)).withPC none) := by
  have hi : ExecSparsifyWorklist.Invariant (ExecutionInvariant z k F)
      (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F)) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using
      executionInvariant_initial z k F hF
  have ht := Ambient.run_trace splitter register stack frame hr hs enc
    (ExecSparsifyWorklist.executableBranching z k hz) (ExecutionInvariant z k F) cost hreal
    (executionInvariant_closed z k hz F)
    (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F)) hi
  simpa only [ExecSparsifyWorklist.executeM_value, ExecSparsifyWorklist.execute,
    ExecSparsifyWorklist.initial, forestWork_cons, forestWork_nil, Nat.add_zero] using ht

/-- A concrete visit-count interface for the actual outer machine. The bound
on the splitter is needed solely for reachable bounded formulas of this run. -/
theorem executeM_primitive (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : ExecSparsifyWorklist.Formula n → List Bool) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (F : ExecSparsifyWorklist.Formula n)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) (cost : ExecSparsifyWorklist.Formula n → ℕ)
    (bound : ℕ)
    (hreal : Ambient.RealizesOn splitter register stack frame enc
      (ExecSparsifyWorklist.splitFormula z k) (ExecutionInvariant z k F) cost)
    (hbound : ∀ G, ExecutionInvariant z k F G →
      cost G + updateCost enc G (ExecSparsifyWorklist.splitFormula z k G) ≤ bound) :
    Computation.RunsIn (BitProgram.primitive (Ambient.program splitter register stack)).step
      (BitProgram.primitiveOverhead (Ambient.program splitter register stack) *
        ((bound + 4) * (ExecSparsifyWorklist.executeM z k hz F).1.visits + 6))
      (BitProgram.primitiveCfg (Ambient.program splitter register stack)
        ((Ambient.liftData register stack frame (canonicalData enc
          (ExecSparsifyWorklist.initial (ExecSparsifyWorklist.normalizedInput F)))).withPC
            (some (Ambient.program splitter register stack).entry)))
      (BitProgram.primitiveCfg (Ambient.program splitter register stack)
        ((Ambient.liftData register stack frame
          (canonicalData enc (ExecSparsifyWorklist.executeM z k hz F).1)).withPC none)) := by
  simpa only [ExecSparsifyWorklist.executeM_value, ExecSparsifyWorklist.execute] using
    Ambient.initial_run_primitive splitter register stack frame hr hs enc
      (ExecSparsifyWorklist.executableBranching z k hz) (ExecutionInvariant z k F) cost bound hreal
      (executionInvariant_closed z k hz F) hbound
      (ExecSparsifyWorklist.normalizedInput F) (executionInvariant_initial z k F hF)

end ConcreteExecution

end SubexponentialSAT.ExecWorklistLoop

end OAI.Algorithms
