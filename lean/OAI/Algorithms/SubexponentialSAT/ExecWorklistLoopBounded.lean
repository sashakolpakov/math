import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoop

namespace OAI.Algorithms

/-!
# Bounded actual splitter traces in the encoded worklist loop

The splitter is still one fixed finite program. For every current node in the
reachable invariant it supplies an actual trace bounded by a local node cost.
The trace length may depend on the framed state. The unchanged worklist code
composes these traces, and its proof sums their upper bounds along the actual
branch tree. No accumulated output length is charged.
-/

namespace SubexponentialSAT.ExecWorklistLoop.Ambient

open BitProgram StructuredCalls

variable {α : Type*} {r s : ℕ}

abbrev BoundedRealizesOn {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (enc : α → List Bool) (split : α → Option (α × α)) (P : α → Prop) (cost : α → ℕ) : Prop :=
  ∀ x, P x → ∀ pending leaves,
    RunsIn splitter (cost x)
      ((liftData register stack frame (loopData enc ⟨x :: pending, leaves, 0⟩)).withPC (some splitter.entry))
      ((liftData register stack frame (splitData enc x pending leaves (split x))).withPC none)

theorem boundedRealizesOn_of_exact {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (enc : α → List Bool) (split : α → Option (α × α)) (P : α → Prop) (cost : α → ℕ)
    (h : RealizesOn splitter register stack frame enc split P cost) :
    BoundedRealizesOn splitter register stack frame enc split P cost := by
  intro x hx pending leaves
  exact ⟨cost x, le_rfl, h x hx pending leaves⟩

theorem BoundedRealizesOn.mono {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (enc : α → List Bool) (split : α → Option (α × α)) (P : α → Prop)
    (cost bound : α → ℕ)
    (h : BoundedRealizesOn splitter register stack frame enc split P cost)
    (hb : ∀ x, P x → cost x ≤ bound x) :
    BoundedRealizesOn splitter register stack frame enc split P bound := by
  intro x hx pending leaves
  exact (h x hx pending leaves).mono (hb x hx)

theorem body_bounded {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : BoundedRealizesOn splitter register stack frame enc branch.split P cost)
    (x : α) (hx : P x) (pending leaves : List α) (visits : ℕ) :
    ∃ n ≤ cost x + updateCost enc x (branch.split x) + 3,
      Eval (body splitter register stack) n
        (liftData register stack frame (loopData enc ⟨x :: pending, leaves, visits⟩))
        (liftData register stack frame
          (loopData enc (ExecSparsifyWorklist.step branch.split ⟨x :: pending, leaves, visits⟩))) := by
  obtain ⟨n, hn, htrace⟩ := hreal x hx pending leaves
  have hsplit : Eval (.call splitter) n
      (liftData register stack frame (loopData enc ⟨x :: pending, leaves, visits⟩))
      (liftData register stack frame (splitData enc x pending leaves (branch.split x))) :=
    .call splitter htrace
  have htail := liftCommand_eval register stack frame hr hs
    (nodeTail_eval enc branch x pending leaves visits)
  refine ⟨n + updateCost enc x (branch.split x) + 3, by omega, ?_⟩
  simpa only [body, Nat.add_assoc] using Eval.seq hsplit htail

/-- The existing finite pending-list loop terminates along the actual
branching run. Its proof-only forest potential is never stored by the code. -/
theorem while_bounded {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : BoundedRealizesOn splitter register stack frame enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (state : ExecSparsifyWorklist.State α) (hstate : ExecSparsifyWorklist.Invariant P state) :
    ∃ n ≤ forestWork enc branch (fun x => cost x + 1) state.pending + 1,
      Eval (.while (register 3) (body splitter register stack)) n
        (liftData register stack frame (loopData enc state))
        (liftData register stack frame (loopData enc (ExecSparsifyWorklist.run branch state))) := by
  induction state using (measure (fun state : ExecSparsifyWorklist.State α =>
      ExecSparsifyWorklist.potential branch.mass state.pending)).wf.induction with
  | h state ih =>
    rcases state with ⟨pending, leaves, visits⟩
    cases pending with
    | nil =>
      have hrun : ExecSparsifyWorklist.run branch ⟨[], leaves, visits⟩ = ⟨[], leaves, visits⟩ := rfl
      refine ⟨1, by simp, ?_⟩
      rw [hrun]
      apply Eval.while_false
      exact (embedState_register register stack frame _ hr 3).trans rfl
    | cons x xs =>
      let state : ExecSparsifyWorklist.State α := ⟨x :: xs, leaves, visits⟩
      have hn : state.pending ≠ [] := by simp [state]
      have hd := ExecSparsifyWorklist.step_potential_lt branch state hn
      have hnext := ExecSparsifyWorklist.step_invariant branch.split P hclosed state hstate
      obtain ⟨nr, hnr, hrec⟩ := ih (ExecSparsifyWorklist.step branch.split state) hd hnext
      have hx : P x := hstate.1 x List.mem_cons_self
      obtain ⟨nb, hnb, hb⟩ := body_bounded splitter register stack frame hr hs
        enc branch P cost hreal x hx xs leaves visits
      have hguard : (liftData register stack frame (loopData enc state)).regs (register 3) = true :=
        (embedState_register register stack frame _ hr 3).trans rfl
      have ht := Eval.while_true hguard hb hrec
      have he := ExecSparsifyWorklist.run_after_step branch state hn
      rw [← he] at ht
      refine ⟨nb + nr + 1, ?_, ht⟩
      have hw := forestWork_step enc branch (fun x => cost x + 1) x xs leaves visits
      change nr ≤ forestWork enc branch (fun x => cost x + 1)
        (ExecSparsifyWorklist.step branch.split ⟨x :: xs, leaves, visits⟩).pending + 1 at hnr
      change nb + nr + 1 ≤ forestWork enc branch (fun x => cost x + 1) (x :: xs) + 1
      rw [hw]
      omega

/-- A cumulative actual finite-program trace with a sum of local upper
bounds. The output is the same actual DFS traversal specified by `run`. -/
theorem run_bounded {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (hreal : BoundedRealizesOn splitter register stack frame enc branch.split P cost)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (state : ExecSparsifyWorklist.State α) (hstate : ExecSparsifyWorklist.Invariant P state) :
    RunsIn (program splitter register stack)
      (forestWork enc branch (fun x => cost x + 1) state.pending + 6)
      ((liftData register stack frame (canonicalData enc state)).withPC
        (some (program splitter register stack).entry))
      ((liftData register stack frame
        (canonicalData enc (ExecSparsifyWorklist.run branch state))).withPC none) := by
  have hp := liftCommand_eval register stack frame hr hs (initialPeek_eval enc state)
  obtain ⟨n, hn, hw⟩ := while_bounded splitter register stack frame hr hs enc branch P cost
    hreal hclosed state hstate
  have hc := liftCommand_eval register stack frame hr hs
    (clearPresent_eval enc (ExecSparsifyWorklist.run branch state)
      (ExecSparsifyWorklist.run_pending_nil branch state))
  have he : Eval (command splitter register stack) (2 + (n + 2))
      (liftData register stack frame (canonicalData enc state))
      (liftData register stack frame
        (canonicalData enc (ExecSparsifyWorklist.run branch state))) :=
    .seq hp (.seq hw hc)
  exact ⟨2 + (n + 2) + 1, by omega, compiled_halt_trace he (stack 0) (stack 1)⟩

/-- The node bound is required only on the preserved reachable invariant.
This supplies the same visit-factor bound without a uniform exact-time
premise on the splitter or any charge for accumulated leaf storage. -/
theorem initial_run_primitive_bounded {labels : ℕ} (splitter : Program r s labels)
    (register : Fin 4 → Fin r) (stack : Fin 5 → Fin s) (frame : StructuredProgram.State r s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop)
    (cost : α → ℕ) (bound : ℕ)
    (hreal : BoundedRealizesOn splitter register stack frame enc branch.split P cost)
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
  obtain ⟨n, hn, htrace⟩ := run_bounded splitter register stack frame hr hs enc branch P cost
    hreal hclosed (ExecSparsifyWorklist.initial x) hi
  have ht := BitProgram.primitive_trace (program splitter register stack) htrace
  apply ht.mono
  apply Nat.mul_le_mul_left
  apply hn.trans
  rw [ExecSparsifyWorklist.initial_run_visits]
  have hb : ∀ y, P y → (cost y + 1) + updateCost enc y (branch.split y) ≤ bound + 1 := by
    intro y hy
    have := hbound y hy
    omega
  have hnode := nodeWork_le_visits enc branch P (fun y => cost y + 1) (bound + 1) hclosed hb x hx
  simpa [ExecSparsifyWorklist.initial, Nat.add_assoc] using Nat.add_le_add_right hnode 6

end SubexponentialSAT.ExecWorklistLoop.Ambient

end OAI.Algorithms
