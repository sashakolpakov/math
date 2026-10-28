import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectGreedy

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure LoopPorts (r s : ℕ) where
  value : Fin r
  present : Fin r
  counter : Fin s
  value_ne_present : value ≠ present

abbrev readCounter {r s : ℕ} (p : LoopPorts r s) : Cmd r s :=
  .base (.atom (.pop p.counter p.value p.present))

def readCounterState {r s : ℕ} (p : LoopPorts r s) (a : State r s) : State r s :=
  ⟨readRegs a.regs p.value p.present (a.stacks p.counter).head?,
    Function.update a.stacks p.counter (a.stacks p.counter).tail⟩

theorem readCounter_eval {r s : ℕ} (p : LoopPorts r s) (a : State r s) :
    Eval (readCounter p) 1 a (readCounterState p a) := .base (.atom _ _)

abbrev rounds {r s : ℕ} (p : LoopPorts r s) (body : Cmd r s) : Cmd r s :=
  .seq (readCounter p) (.while p.present (.seq body (readCounter p)))

abbrev iter {α : Type*} (next : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => iter next n (next x)

/-- Invariance under the actual counter read and the paid round execution.
This is an integration contract, not an existence claim for the round code. -/
structure RoundSpec {r s : ℕ} {α : Type*} (p : LoopPorts r s) (body : Cmd r s)
    (next : α → α) (invariant : α → State r s → Prop) (cost : ℕ) : Prop where
  read : ∀ x a, invariant x a → invariant x (readCounterState p a)
  step : ∀ x a, invariant x a → a.regs p.present = true →
    ∃ n ≤ cost, ∃ b, invariant (next x) b ∧
      b.stacks p.counter = a.stacks p.counter ∧ b.regs p.present = true ∧
      Eval body n a b

def roundsBudget (cost count : ℕ) : ℕ := count * (cost + 2) + 2

theorem rounds_eval {r s : ℕ} {α : Type*} (p : LoopPorts r s) (body : Cmd r s)
    (next : α → α) (invariant : α → State r s → Prop) (cost : ℕ)
    (h : RoundSpec p body next invariant cost)
    (x : α) (depth : List Bool) (a : State r s)
    (hi : invariant x a) (hd : a.stacks p.counter = depth) :
    ∃ n ≤ roundsBudget cost depth.length, ∃ b,
      invariant (iter next depth.length x) b ∧
      b.stacks p.counter = [] ∧ b.regs p.present = false ∧ Eval (rounds p body) n a b := by
  induction depth generalizing x a with
  | nil =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = [] := by simp [b, readCounterState, hd]
    have hf : b.regs p.present = false := by simp [b, readCounterState, hd, readRegs]
    refine ⟨2, by simp [roundsBudget], b, h.read x a hi, hb, hf, ?_⟩
    exact Eval.seq (readCounter_eval p a) (Eval.while_false hf)
  | cons bit depth ih =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = depth := by simp [b, readCounterState, hd]
    have ht : b.regs p.present = true := by simp [b, readCounterState, hd, readRegs]
    obtain ⟨u, hu, c, hc, hcounter, hguard, he⟩ := h.step x b (h.read x a hi) ht
    obtain ⟨t, ht', d, hi', hd', hf', he'⟩ := ih (next x) c hc (hcounter.trans hb)
    cases he' with
    | @seq first second n m a' b' c' hread hloop =>
      refine ⟨1 + (u + n + m + 1), ?_, d, hi', hd', hf', ?_⟩
      · simp only [roundsBudget, List.length_cons] at ht' ⊢
        nlinarith
      · exact Eval.seq (readCounter_eval p a)
          (Eval.while_true ht (Eval.seq he hread) hloop)

abbrev roundsProgram {r s : ℕ} (p : LoopPorts r s) (body : Cmd r s)
    (output : Fin s) := compiled (rounds p body) p.counter output

theorem roundsProgram_trace {r s : ℕ} {α : Type*} (p : LoopPorts r s)
    (body : Cmd r s) (output : Fin s) (next : α → α)
    (invariant : α → State r s → Prop) (cost : ℕ)
    (h : RoundSpec p body next invariant cost)
    (x : α) (depth : List Bool) (a : State r s)
    (hi : invariant x a) (hd : a.stacks p.counter = depth) :
    ∃ n ≤ roundsBudget cost depth.length + 1, ∃ b,
      invariant (iter next depth.length x) b ∧ b.stacks p.counter = [] ∧
      Trace (roundsProgram p body output) n
        (a.withPC (some (roundsProgram p body output).entry)) (b.withPC none) := by
  obtain ⟨n, hn, b, hi', hd', _, ht⟩ := rounds_eval p body next invariant cost h x depth a hi hd
  exact ⟨n + 1, Nat.add_le_add_right hn 1, b, hi', hd', compiled_halt_trace ht _ _⟩

theorem iter_succ_apply {α : Type*} (next : α → α) (n : ℕ) (x : α) :
    iter next (n + 1) x = next (iter next n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [iter] using ih (next x)

/-- The runtime controller's recurrence agrees with the semantic hash loop. -/
theorem iter_hash_run {R : Type*} {c : ℕ} (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (n : ℕ) :
    iter (HashSelect.next evaluate family) n initial = HashSelect.run evaluate family initial n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ_apply, HashSelect.run, ih]

/-- A bounded variant lets the callback cost depend on a certified maximum
number of rows. The bound is used only at iterations that actually run. -/
structure BoundedRoundSpec {r s : ℕ} {α : Type*} (p : LoopPorts r s)
    (body : Cmd r s) (next : α → α) (invariant : ℕ → α → State r s → Prop)
    (cost limit : ℕ) : Prop where
  read : ∀ q x a, invariant q x a → invariant q x (readCounterState p a)
  step : ∀ q x a, q < limit → invariant q x a → a.regs p.present = true →
    ∃ n ≤ cost, ∃ b, invariant (q + 1) (next x) b ∧
      b.stacks p.counter = a.stacks p.counter ∧ b.regs p.present = true ∧
      Eval body n a b

theorem rounds_eval_bounded {r s : ℕ} {α : Type*} (p : LoopPorts r s)
    (body : Cmd r s) (next : α → α) (invariant : ℕ → α → State r s → Prop)
    (cost limit : ℕ) (h : BoundedRoundSpec p body next invariant cost limit)
    (q : ℕ) (x : α) (depth : List Bool) (a : State r s)
    (hq : q + depth.length ≤ limit) (hi : invariant q x a)
    (hd : a.stacks p.counter = depth) :
    ∃ n ≤ roundsBudget cost depth.length, ∃ b,
      invariant (q + depth.length) (iter next depth.length x) b ∧
      b.stacks p.counter = [] ∧ b.regs p.present = false ∧ Eval (rounds p body) n a b := by
  induction depth generalizing q x a with
  | nil =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = [] := by simp [b, readCounterState, hd]
    have hf : b.regs p.present = false := by simp [b, readCounterState, hd, readRegs]
    refine ⟨2, by simp [roundsBudget], b, h.read q x a hi, hb, hf, ?_⟩
    exact Eval.seq (readCounter_eval p a) (Eval.while_false hf)
  | cons bit depth ih =>
    let b := readCounterState p a
    have hb : b.stacks p.counter = depth := by simp [b, readCounterState, hd]
    have ht : b.regs p.present = true := by simp [b, readCounterState, hd, readRegs]
    obtain ⟨u, hu, c, hc, hcounter, hguard, he⟩ :=
      h.step q x b (by simp only [List.length_cons] at hq; omega) (h.read q x a hi) ht
    obtain ⟨t, ht', d, hi', hd', hf', he'⟩ := ih (q + 1) (next x) c
      (by simp only [List.length_cons] at hq; omega) hc (hcounter.trans hb)
    cases he' with
    | @seq first second n m a' b' c' hread hloop =>
      refine ⟨1 + (u + n + m + 1), ?_, d, ?_, hd', hf', ?_⟩
      · simp only [roundsBudget, List.length_cons] at ht' ⊢
        nlinarith
      · simpa only [iter, List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hi'
      · exact Eval.seq (readCounter_eval p a)
          (Eval.while_true ht (Eval.seq he hread) hloop)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
