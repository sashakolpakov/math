import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

/-! Prefix composition for the actual exhausted and leaf branches of the
attained-signature controller. The component executions are the installed
probe, visitor and ascent commands, and every caller stack is covered. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative

/-- Inverting the installed body preserves its actual measured execution;
it does not choose a second run or replace the visitor. -/
theorem iteration_of_eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (he : Eval (body p q) n a b) :
    Iteration p q n a b := by
  cases he with
  | ite_true hl hleaf =>
    cases hleaf with
    | seq hv ha => exact .leaf hl hv ha
  | ite_false hl hscan =>
    cases hscan with
    | seq hp havailable =>
      cases havailable with
      | ite_false ha hasc =>
        simpa only [Nat.add_assoc] using Iteration.exhausted hl hp ha hasc
      | ite_true ha hfresh =>
        cases hfresh with
        | ite_true hf hd =>
          simpa only [Nat.add_assoc] using Iteration.fresh hl hp ha hf hd
        | ite_false hf hn =>
          simpa only [Nat.add_assoc] using Iteration.duplicate hl hp ha hf hn

theorem exhausted_body_eval (load visit : Cmd 40 896)
    (a b c : State 40 896) (np na : ℕ)
    (hl : a.regs controllerPorts.leaf = false)
    (ha : b.regs controllerPorts.available = false)
    (hp : Eval (probeWith candidateCall) np a b)
    (hasc : Eval (ascendWith load) na b c) :
    Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (np + na + 2) a c :=
  (Iteration.exhausted hl hp ha hasc).eval

theorem leaf_body_eval (load visit : Cmd 40 896)
    (a b c : State 40 896) (nv na : ℕ)
    (hl : a.regs controllerPorts.leaf = true)
    (hv : Eval visit nv a b) (hasc : Eval (ascendWith load) na b c) :
    Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (nv + na + 1) a c :=
  (Iteration.leaf hl hv hasc).eval

/-- An exhausted cursor takes the available=false branch, ascends, and
halts without allocating another word or invoking the leaf visitor. -/
theorem exhausted_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (np na D : ℕ)
    (hl : a.regs controllerPorts.leaf = false)
    (ha : b.regs controllerPorts.available = false)
    (hp : Eval (probeWith candidateCall) np a b)
    (hasc : Eval (ascendWith load) na b c)
    (hps : ∀ p q, p ≤ np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D)
    (has : ∀ p q, p ≤ na → Trace (compiled (ascendWith load) 0 0) p
      (b.withPC (some (compiled (ascendWith load) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D) :
    ∀ p q, p ≤ np + na + 3 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D := by
  let freshBranch : Cmd 40 896 :=
    .ite controllerPorts.fresh (descendWith load) advanceCandidateCommand
  let availableBranch : Cmd 40 896 :=
    .ite controllerPorts.available freshBranch (ascendWith load)
  have hae : Eval availableBranch (na + 1) b c := .ite_false ha hasc
  have haspace := StructuredSpace.conditional_false_stack_bound
    (yes := freshBranch) ha hasc 0 0 has
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq hae
  have hsseq := StructuredSpace.sequence_stack_bound hp hae 0 0 hps haspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (np + (na + 1) + 1) a c := .ite_false hl hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith load)) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i

/-- Visiting one attained tuple and ascending share the same space cap,
including the outer branch instruction and final compiled halt. -/
theorem leaf_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (nv na D : ℕ)
    (hl : a.regs controllerPorts.leaf = true)
    (hv : Eval visit nv a b) (hasc : Eval (ascendWith load) na b c)
    (hvs : ∀ p q, p ≤ nv → Trace (compiled visit 0 0) p
      (a.withPC (some (compiled visit 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D)
    (has : ∀ p q, p ≤ na → Trace (compiled (ascendWith load) 0 0) p
      (b.withPC (some (compiled (ascendWith load) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D) :
    ∀ p q, p ≤ nv + na + 2 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D := by
  have hseq := hv.seq hasc
  have hsseq := StructuredSpace.sequence_stack_bound hv hasc 0 0 hvs has
    (compiled (.seq visit (ascendWith load)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he := leaf_body_eval load visit a b c nv na hl hv hasc
  have hwhole := StructuredSpace.conditional_true_stack_bound
    (no := .seq (probeWith candidateCall)
      (.ite controllerPorts.available
        (.ite controllerPorts.fresh (descendWith load) advanceCandidateCommand)
        (ascendWith load))) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
