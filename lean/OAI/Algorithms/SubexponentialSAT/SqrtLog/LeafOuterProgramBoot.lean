import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramMain
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionBoot

namespace OAI.Algorithms

/-! Direct join from the actual post-splitter state to the measured new leaf
callback.  The remaining core contract is precisely a native whole-leaf trace,
not a setup, splitter, parser-frame, or restoration assumption. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Execution

theorem boot_invariant {c : SubexponentialSAT.SubexpSetupProgram.Config}
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) {n : ℕ}
    {hr : 32 ≤ workRegs finalExtraRegisters} {F : SubexpOrderedRawPrefix.Formula n}
    (r : Boot c finalExtraRegisters hr F) :
    Invariant c hc
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)) r.final := by
  constructor
  · intro i
    exact r.outcome.workspace _ (WideLeaf.stack_lt_helper c hc i)
  · exact (r.outcome.persistent_frame 9 (by decide) (by decide)).trans
      (r.startup.empty 9 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact (r.outcome.persistent_frame 10 (by decide) (by decide)).trans
      (r.startup.empty 10 (by decide) (by decide) (by decide) (by decide) (by decide))
  · rfl
  · rfl

noncomputable abbrev boot_execution {c : SubexponentialSAT.SubexpSetupProgram.Config}
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) {n : ℕ}
    {hr : 32 ≤ workRegs finalExtraRegisters} {F : SubexpOrderedRawPrefix.Formula n}
    (r : Boot c finalExtraRegisters hr F)
    (leafPhases : Phases finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c))
    (core : Cmd 40 896) (test : List Bool → Bool) (coreCost : List Bool → ℕ)
    (valid : List Bool → Prop)
    (hcore : CoreContract core test coreCost valid
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)))
    (hvalid : ∀ bits ∈ r.records, valid bits)
    (hspec : ∀ G ∈ r.leaves, test (ExecSparsifyObserved.encode G)=true ↔
      SAT.Satisfiable (ExecCNF.formulaSet G)) :
    SubexpOrderedRawRuntime.Execution (phases c hr leafPhases)
      (singleLeaf (LeafMain.procedure c hc core)) F :=
  r.toExecution leafPhases (singleLeaf (LeafMain.procedure c hc core)) test
    (callbackCost coreCost
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)))
    (Invariant c hc
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24))) valid
    (callback_contract c hc core test coreCost valid _ _ hcore) hvalid
    (boot_invariant hc r) hspec

end SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter

end OAI.Algorithms
