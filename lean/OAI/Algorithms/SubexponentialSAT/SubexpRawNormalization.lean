import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNormalization

namespace OAI.Algorithms

/-! The actual raw frontend followed by retained-body normalization. -/

namespace SubexponentialSAT.SubexpRawNormalization

open BitProgram StructuredCalls SubexpMainProgram

theorem work_ne_persistent (es : ℕ) (i : Fin 17) (j : Fin 32) :
    SubexpMainNormalization.workPort es i ≠ persistent es j := by
  intro h
  have hv := congrArg (fun i : Fin (totalStacks es) => i.val) h
  have := i.isLt
  change i.val = 128 + es + j.val at hv
  omega

theorem prefix_slot (er es : ℕ) (input body nb sb ub : List Bool) (i : Fin 6) :
    (prefixData er es input body nb sb ub).stacks (persistent es (i.castAdd 26)) =
      (SubexpFrontendPrefix.state body nb sb ub).stacks i :=
  embedState_stack (frontendProcedure er es).registerMap (frontendProcedure er es).stack
    (initialData er es input) (SubexpFrontendPrefix.state body nb sb ub)
    (frontendProcedure er es).stack.injective i

theorem prefix_workspace_clean (er es : ℕ) (input body nb sb ub : List Bool) :
    SubexpMainNormalization.WorkspaceClean (prefixData er es input body nb sb ub) := by
  intro i
  have hframe : (prefixData er es input body nb sb ub).stacks
      (SubexpMainNormalization.workPort es i) =
      (initialData er es input).stacks (SubexpMainNormalization.workPort es i) := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    exact work_ne_persistent es i (j.castAdd 26) hj.symm
  rw [hframe]
  simp [initialData, StructuredProgram.ioState, work_ne_persistent]

def command (er es : ℕ) : MainCmd er es :=
  .seq (frontendProcedure er es).invoke (SubexpMainNormalization.procedure er es).invoke

/-- Raw parsing and parameter construction physically precede normalization.
The n/s/u words survive the normalization phase exactly. -/
theorem command_eval (er es : ℕ) {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ (nb sb ub : List Bool) (t : ℕ) (out : MainState er es),
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      t ≤ 3599 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      Eval (command er es) t (initialData er es (Encoding.encodeCNF F)) out ∧
      SubexpMainNormalization.WorkspaceClean out ∧
      out.stacks (persistent es 0) = SubexpNormalizationCorrectness.normalizedBody F ∧
      out.stacks (persistent es 2) = nb ∧
      out.stacks (persistent es 4) = sb ∧
      out.stacks (persistent es 5) = ub := by
  obtain ⟨nb, sb, ub, t, hn, hs, hu, ht, hprefix⟩ := prefix_execution er es F
  let a := prefixData er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub
  have ha0 : a.stacks (persistent es 0) = Encoding.encodeCNFBody F := by
    simpa [a, SubexpFrontendPrefix.state, SubexpFrontendPrefix.storage] using
      prefix_slot er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub 0
  have ha2 : a.stacks (persistent es 2) = nb := by
    simpa [a, SubexpFrontendPrefix.state, SubexpFrontendPrefix.storage] using
      prefix_slot er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub 2
  have ha4 : a.stacks (persistent es 4) = sb := by
    simpa [a, SubexpFrontendPrefix.state, SubexpFrontendPrefix.storage] using
      prefix_slot er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub 4
  have ha5 : a.stacks (persistent es 5) = ub := by
    simpa [a, SubexpFrontendPrefix.state, SubexpFrontendPrefix.storage] using
      prefix_slot er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub 5
  obtain ⟨u, hubound, out, hnorm, hwork, hbody, hframe, _⟩ :=
    SubexpMainNormalization.invoke_canonical F a ha0
      (prefix_workspace_clean er es _ _ _ _ _)
  have hlen : (Encoding.encodeCNFBody F).length + 1 ≤ Encoding.formulaBitLength F + 1 := by
    rw [Encoding.formulaBitLength_eq]
    omega
  have hubound' : u ≤ 3500 * (Encoding.formulaBitLength F + 1) ^ 2 :=
    hubound.trans (Nat.mul_le_mul_left 3500 (Nat.pow_le_pow_left hlen 2))
  refine ⟨nb, sb, ub, t + u, out, hn, hs, hu, ?_, hprefix.seq hnorm,
    hwork, hbody, (hframe 2 (by decide)).trans ha2,
    (hframe 4 (by decide)).trans ha4, (hframe 5 (by decide)).trans ha5⟩
  rw [SubexpFrontendPrefix.bound_eq] at ht
  nlinarith

def program (er es : ℕ) := compiled (command er es) (persistent es 0) (persistent es 0)

theorem program_runsIn (er es : ℕ) {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ (nb sb ub : List Bool) (out : MainState er es),
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      SubexpMainNormalization.WorkspaceClean out ∧
      out.stacks (persistent es 0) = SubexpNormalizationCorrectness.normalizedBody F ∧
      out.stacks (persistent es 2) = nb ∧
      out.stacks (persistent es 4) = sb ∧
      out.stacks (persistent es 5) = ub ∧
      RunsIn (program er es) (3600 * (Encoding.formulaBitLength F + 1) ^ 2)
        (initial (program er es) (Encoding.encodeCNF F)) (out.withPC none) := by
  obtain ⟨nb, sb, ub, t, out, hn, hs, hu, ht, he, hw, hb, h2, h4, h5⟩ := command_eval er es F
  refine ⟨nb, sb, ub, out, hn, hs, hu, hw, hb, h2, h4, h5, t + 1, ?_,
    compiled_halt_trace he (persistent es 0) (persistent es 0)⟩
  have hpos : 0 < (Encoding.formulaBitLength F + 1) ^ 2 := pow_pos (by omega) _
  omega

theorem primitive_execution (er es : ℕ) {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ (nb sb ub : List Bool) (out : MainState er es),
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      SubexpMainNormalization.WorkspaceClean out ∧
      out.stacks (persistent es 0) = SubexpNormalizationCorrectness.normalizedBody F ∧
      out.stacks (persistent es 2) = nb ∧
      out.stacks (persistent es 4) = sb ∧
      out.stacks (persistent es 5) = ub ∧
      Computation.RunsIn (primitive (program er es)).step
        (primitiveOverhead (program er es) * (3600 * (Encoding.formulaBitLength F + 1) ^ 2))
        ((primitive (program er es)).init (Encoding.encodeCNF F))
        (primitiveCfg (program er es) (out.withPC none)) := by
  obtain ⟨nb, sb, ub, out, hn, hs, hu, hw, hb, h2, h4, h5, hr⟩ := program_runsIn er es F
  exact ⟨nb, sb, ub, out, hn, hs, hu, hw, hb, h2, h4, h5, by
    simpa only [primitive_initial] using BitProgram.primitive_execution (program er es) hr⟩

end SubexponentialSAT.SubexpRawNormalization

end OAI.Algorithms
