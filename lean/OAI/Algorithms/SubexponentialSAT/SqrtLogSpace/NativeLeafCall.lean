import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

/-! Concrete shared-ABI leaf calls retain the caller storage bound through every
callee instruction, including its compiled halt/return. Off-leaf caller contents
are preserved at every prefix; the entire local output word is read at1108. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
open BitProgram StructuredCalls DisjointReuse.DFSVisit

private theorem leafCall_code {l : ℕ} (p : Program 40 896 l) :
    ProgramLinking.CodeEmbedding p (compiled (ABI.leafCall p) 256 256)
      ABI.leafRegisters ABI.leafStacks (siteAddress (ABI.leafCall p))
      (some (exitAddress (ABI.leafCall p))) := by
  intro pc
  unfold ABI.leafCall
  rw [compiled_site]
  change ProgramLinking.relocateInstr id id (siteAddress (ABI.leafCall p))
    (some (exitAddress (ABI.leafCall p)))
    (ProgramLinking.relocateInstr ABI.leafRegisters ABI.leafStacks id none (p.code pc)) = _
  cases p.code pc <;> rfl

private theorem leafCall_start {l : ℕ} (p : Program 40 896 l) (a : State 80 1220) :
    ProgramLinking.embedCfg ABI.leafRegisters ABI.leafStacks
      (siteAddress (ABI.leafCall p)) (some (exitAddress (ABI.leafCall p)))
      (a.withPC none)
      ((projectState ABI.leafRegisters ABI.leafStacks a).withPC (some p.entry)) =
      a.withPC (some (compiled (ABI.leafCall p) 256 256).entry) := by
  change (embedState ABI.leafRegisters ABI.leafStacks a
    (projectState ABI.leafRegisters ABI.leafStacks a)).withPC
    (some (siteAddress (ABI.leafCall p) p.entry)) = _
  rw [embedState_project ABI.leafRegisters ABI.leafStacks a
    ABI.leafRegisters.injective ABI.leafStacks.injective]
  rfl

theorem leafCall_bounded_eval {steps localBound bound : ℕ} (command : Cmd 40 896)
    (a : State 80 1220) (b : State 40 896)
    (he : Eval command steps (projectState ABI.leafRegisters ABI.leafStacks a) b)
    (hl : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled command 784 788) prefixSteps
        ((projectState ABI.leafRegisters ABI.leafStacks a).withPC
          (some (compiled command 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (ha : ∀ i, (a.stacks i).length ≤ bound) (hbound : localBound ≤ bound) :
    BoundedEval (ABI.leafCall (compiled command 784 788)) (steps + 1) a
      (embedState ABI.leafRegisters ABI.leafStacks a b) bound := by
  let p := compiled command 784 788
  have ht := compiled_halt_trace he 784 788
  have hs := StructuredSpace.compiled_halt_stack_bound he 784 788 hl
  have hc := eval_call_from_state p ABI.leafRegisters ABI.leafStacks a
    ABI.leafRegisters.injective ABI.leafStacks.injective ht
  have hp := StructuredSpace.relocate_trace_stack_bound p
    (compiled (ABI.leafCall p) 256 256) ABI.leafRegisters ABI.leafStacks
    (siteAddress (ABI.leafCall p)) (some (exitAddress (ABI.leafCall p)))
    (a.withPC none) ABI.leafRegisters.injective ABI.leafStacks.injective
    (leafCall_code p) ht hs ha
  rw [leafCall_start p a] at hp
  refine ⟨hc, ?_⟩
  intro t c htc htr i
  exact (hp t c htc htr i).trans (max_le hbound le_rfl)

theorem leafCall_prefix_frame {steps : ℕ} (command : Cmd 40 896)
    (a : State 80 1220) (b : State 40 896)
    (he : Eval command steps (projectState ABI.leafRegisters ABI.leafStacks a) b)
    {prefixSteps : ℕ} {c : Cfg 80 1220 (size (ABI.leafCall (compiled command 784 788)) + 1)}
    (hle : prefixSteps ≤ steps + 1)
    (hp : Trace (compiled (ABI.leafCall (compiled command 784 788)) 256 256) prefixSteps
      (a.withPC (some (compiled (ABI.leafCall (compiled command 784 788)) 256 256).entry)) c)
    (i : Fin 1220) (hi : ¬ ∃ j, ABI.leafStacks j = i) :
    c.stacks i = a.stacks i := by
  let p := compiled command 784 788
  have ht := compiled_halt_trace he 784 788
  rw [← leafCall_start p a] at hp
  exact StreamResources.relocate_trace_stack_frame p
    (compiled (ABI.leafCall p) 256 256) ABI.leafRegisters ABI.leafStacks
    (siteAddress (ABI.leafCall p)) (some (exitAddress (ABI.leafCall p)))
    (a.withPC none) ABI.leafRegisters.injective ABI.leafStacks.injective
    (leafCall_code p) ht hle hp i hi

theorem leafResult_output (a : State 80 1220) (b : State 40 896) :
    (embedState ABI.leafRegisters ABI.leafStacks a b).stacks 1108 = b.stacks 788 := by
  exact embedState_stack ABI.leafRegisters ABI.leafStacks a b ABI.leafStacks.injective 788

theorem leafResult_frame (a : State 80 1220) (b : State 40 896)
    (i : Fin 1220) (hi : ¬ ∃ j, ABI.leafStacks j = i) :
    (embedState ABI.leafRegisters ABI.leafStacks a b).stacks i = a.stacks i :=
  embedState_stack_frame ABI.leafRegisters ABI.leafStacks a b i hi

theorem leafResult_dfs_stack (a : State 80 1220) (b : State 40 896) (i : Fin 320) :
    (embedState ABI.leafRegisters ABI.leafStacks a b).stacks (ABI.dfsStacks i) =
      a.stacks (ABI.dfsStacks i) := by
  apply leafResult_frame
  rintro ⟨j, hj⟩
  exact ABI.dfs_leaf_stacks_disjoint i j hj.symm

theorem leafResult_dfs_register (a : State 80 1220) (b : State 40 896) (i : Fin 32) :
    (embedState ABI.leafRegisters ABI.leafStacks a b).regs (ABI.dfsRegisters i) =
      a.regs (ABI.dfsRegisters i) := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  exact ABI.dfs_leaf_registers_disjoint i j hj.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
