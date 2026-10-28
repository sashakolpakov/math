import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalBoot
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalCore

namespace OAI.Algorithms

/-! Exact remaining service boundary for the final solver.  The native
services are required only on nontrivial leaves of an actual splitter run. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Filter
open LeafOuterProgram
open scoped Topology

abbrev FinalBoot (c : SubexponentialSAT.SubexpSetupProgram.Config) {n : ℕ}
    (F : SubexpOrderedRawPrefix.Formula n) :=
  Boot c finalExtraRegisters (by decide) F

noncomputable def tailCost (Ct At : ℝ) (dt n : ℕ) (nw Bw : List Bool) (bits : List Bool) : ℕ :=
  Nat.ceil (Statement.runtimeBound Ct At dt (bits.length+nw.length+Bw.length+1) n)

/-- This quantifies over measured native traces, never semantic instructions.
Both metadata words retain their actual physical padding. -/
abbrev ObservedHistoryContract (c : SubexponentialSAT.SubexpSetupProgram.Config)
    (mass acceptedCount : Cmd 40 896) (Ct At : ℝ) (dt : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ F : SubexpOrderedRawPrefix.Formula n,
    ExecSunflowerSearch.RawWidthAtMost c.k F → ∀ r : FinalBoot c F,
    ∀ G ∈ r.leaves, ∀ a : Data,
    MainAdapter.CoreInput a (inputBits G)
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
      (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)) →
    G≠[] → [] ∉ G →
    HistorySupply G (occurrence c n) mass acceptedCount a
      (tailCost Ct At dt n
        (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2))
        (r.final.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24))
        (inputBits G))

/-- A concrete finite leaf procedure also fills the unused standard phase
fields; the actual controller invokes the single custom leaf procedure. -/
abbrev finalLeafPhases (c : SubexponentialSAT.SubexpSetupProgram.Config)
    (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c)
    (mass acceptedCount : Cmd 40 896) :
    Phases finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) :=
  let p := LeafMain.procedure c hc (command mass acceptedCount)
  ⟨p,p,p,p,p,p⟩

end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
