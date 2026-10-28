import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeSetup
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeScratch
import OAI.Algorithms.SubexponentialSAT.SubexpNodeConcretePipeline

namespace OAI.Algorithms

/-! The fixed Main moment phase. Its first part physically prepares the
node workspace; its second part is the concrete widened all-node program.
The same-layout semantic theorem is supplied after the concrete per-node
producer contracts are joined. The transfer rules below concern actual
machine traces and do not assume a semantic node oracle. -/

namespace SubexponentialSAT.SubexpMainMoments

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

def collector (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 352
  labels := size (SubexpNodeWideLoop.command SubexpNodeConcretePipeline.worker) + 1
  program := SubexpNodeConcretePipeline.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨SubexpMainMomentPorts.stackMap alloc, SubexpMainMomentPorts.stackMap_injective alloc⟩

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainNodeSetup.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainNodeScratch.procedure er alloc) (collector er alloc))

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  (procedure er alloc).program

def projected {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    SubexpNodeWideLoop.Data := (collector er alloc).project a

noncomputable def installed {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) : MainState er es :=
  (collector er alloc).install a out

theorem collector_invocation {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) (n : ℕ)
    (h : RunsIn SubexpNodeConcretePipeline.program n
      ((projected alloc a).withPC (some SubexpNodeConcretePipeline.program.entry))
      (out.withPC none)) :
    ∃ m ≤ n, Eval (collector er alloc).invoke m a (installed alloc a out) := by
  obtain ⟨m, hm, ht⟩ := h
  exact ⟨m, hm, Procedure.invoke_trace _ _ _ ht⟩

theorem installed_stack {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) (i : Fin 352) :
    (installed alloc a out).stacks (SubexpMainMomentPorts.stackMap alloc i) = out.stacks i :=
  embedState_stack (collector er alloc).registerMap (collector er alloc).stack
    a out (collector er alloc).stack.injective i

theorem installed_nodes {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) :
    (installed alloc a out).stacks (ordinary alloc 256) = out.stacks 288 :=
  installed_stack alloc a out 288

theorem installed_jets {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) :
    (installed alloc a out).stacks (ordinary alloc 265) = out.stacks 297 :=
  installed_stack alloc a out 297

theorem installed_static {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) (i : Fin 32) :
    (installed alloc a out).stacks (master alloc i) =
      out.stacks ⟨256 + i.val, by omega⟩ := by
  simpa only [SubexpMainMomentPorts.stackMap_static] using
    installed_stack alloc a out ⟨256 + i.val, by omega⟩

theorem installed_crt_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) (i : Fin (totalStacks es))
    (hlo : 320 ≤ i.val) (hhi : i.val < 640) :
    (installed alloc a out).stacks i = a.stacks i :=
  embedState_stack_frame _ _ _ _ _ (SubexpMainMomentPorts.stackMap_avoids_crt alloc i hlo hhi)

theorem installed_controls {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpNodeWideLoop.Data) (i : Fin 3) :
    (installed alloc a out).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ i

/-- Exact composition of the real setup invocation with a real trace of
the installed concrete collector. This is the physical transfer used by
the final ordered-node correctness theorem. -/
theorem compose_runs {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (out : SubexpNodeWideLoop.Data) (n m : ℕ)
    (hsetup : Eval (SubexpMainNodeSetup.procedure er alloc).invoke n a b)
    (hcollect : RunsIn SubexpNodeConcretePipeline.program m
      ((projected alloc (SubexpMainNodeScratch.result alloc b)).withPC
        (some SubexpNodeConcretePipeline.program.entry))
      (out.withPC none)) :
    ∃ steps ≤ n + SubexpMainNodeScratch.runtimeBound alloc b + m + 2,
      Eval (procedure er alloc).invoke steps a
        (installed alloc (SubexpMainNodeScratch.result alloc b) out) := by
  obtain ⟨mc, hmc, hc⟩ := collector_invocation alloc
    (SubexpMainNodeScratch.result alloc b) out m hcollect
  exact ⟨n + (SubexpMainNodeScratch.runtimeBound alloc b + mc + 1) + 1, by omega,
    SubexpProcedureCompose.sequence_invoke _ _ hsetup
      (SubexpProcedureCompose.sequence_invoke _ _ (SubexpMainNodeScratch.execution alloc b) hc)⟩

end SubexponentialSAT.SubexpMainMoments

end OAI.Algorithms
