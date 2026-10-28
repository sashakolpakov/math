import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeSetupSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

/-! Every-prefix space composition for the actual canonical frontend and
fixed-cutoff dispatcher. The large evaluation is a concrete subsequent run;
this module only composes its existing bound with the paid entry instructions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse.DFSVisit

theorem frontend_bounded_eval {n frontSteps bound : ℕ} (F : SAT.CNF (Fin n))
    (a : State 80 1220)
    (he : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (ht : frontSteps ≤ frontendBound F)
    (hbudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound) :
    BoundedEval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a bound := by
  refine ⟨he, ?_⟩
  intro prefixSteps c hp hc i
  have hsize : dataBits
      ((StructuredProgram.ioState (r := 80) ABI.countStack (Encoding.encodeCNF F)).withPC
        (some (compiled frontendCommand 256 256).entry)) ≤ Encoding.formulaBitLength F := by
    change dataBits (initial (compiled frontendCommand 256 256) (Encoding.encodeCNF F)) ≤ _
    simp [Encoding.formulaBitLength]
  have htime := ht.trans (frontendBound_polynomial F)
  exact (StructuredSpace.local_stack_bound (compiled frontendCommand 256 256)
    (steps := 4000 * (Encoding.formulaBitLength F + 1) ^ 2)
    hsize prefixSteps c (hp.trans htime) hc i).trans hbudget

/-- Obtain the frontend state, its binary dimension, and its source prefix
bound from the actual canonical-input evaluation theorem. -/
theorem frontend_bounded {n bound : ℕ} (F : SAT.CNF (Fin n))
    (hbudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound) :
    ∃ binary frontSteps a, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      frontSteps ≤ frontendBound F ∧
      BoundedEval frontendCommand frontSteps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a bound ∧
      FrontendReady F binary a := by
  obtain ⟨binary, frontSteps, a, hv, hl, ht, he, ready⟩ := frontend_eval F
  exact ⟨binary, frontSteps, a, hv, hl, ht,
    frontend_bounded_eval F a he ht hbudget, ready⟩

/-- The fixed-cutoff scan has polynomial local space and the same bound is
retained on every prefix of the following actual large-input evaluation. -/
theorem entry_large_bounded_eval {cutoff n frontSteps steps bound : ℕ}
    (large : Cmd 80 1220) (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a b : State 80 1220) (hn : cutoff < n)
    (hfront : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (hfrontTime : frontSteps ≤ frontendBound F)
    (ready : FrontendReady F binary a) (hlen : binary.length ≤ n)
    (hfrontBudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound)
    (hdispatchBudget : 1224 * (Encoding.formulaBitLength F + 1) + 10 * n + 28 ≤ bound)
    (hlarge : BoundedEval large steps (FiniteFallback.cutoffResult a false) b bound) :
    BoundedEval (entryCommand cutoff large) (frontSteps + (10 * n + 29 + steps))
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound := by
  have hf := frontend_bounded_eval F a hfront hfrontTime hfrontBudget
  have hframe := frontendReady_stack_bound F binary a ready hlen
  have hd := FiniteFallback.dispatch_large_eval large hn a b ready.header hlarge.eval
  have hs := FiniteFallback.dispatch_large_space large hn a b ready.header hframe
    hdispatchBudget hlarge.eval hlarge.space
  have h270 := ready.blank 270 (by decide) (by decide) (by decide) (by decide)
  have h271 := ready.blank 271 (by decide) (by decide) (by decide) (by decide)
  rw [h270, h271] at hd hs
  have hb : BoundedEval (FiniteFallback.dispatchCommand cutoff large)
      (10 * n + 29 + steps) a b bound := ⟨by simpa using hd, by simpa using hs⟩
  exact hf.seq hb

/-- The terminal halt and the selected Boolean output metadata preserve the
same entry bound. The primitive compiler can consume this exact source trace. -/
theorem entry_bounded_trace_space {cutoff steps bound : ℕ} (large : Cmd 80 1220)
    (input : List Bool) (b : State 80 1220)
    (he : BoundedEval (entryCommand cutoff large) steps
      (StructuredProgram.ioState ABI.countStack input) b bound) :
    Trace (entryProgram cutoff large) (steps + 1)
      (initial (entryProgram cutoff large) input) (b.withPC none) ∧
    ∀ prefixSteps c, prefixSteps ≤ steps + 1 →
      Trace (entryProgram cutoff large) prefixSteps
        (initial (entryProgram cutoff large) input) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  refine ⟨compiled_halt_trace he.eval ABI.countStack ABI.answerStack, ?_⟩
  exact StructuredSpace.compiled_halt_stack_bound he.eval ABI.countStack ABI.answerStack he.space

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
