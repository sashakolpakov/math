import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawRecordFacts
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawRuntime

namespace OAI.Algorithms

/-! Actual ordered boot and record facts drive the same physical controller. -/
namespace SubexponentialSAT.SubexpOrderedRawAssembly
open SubexpMainProgram SubexpSetupProgram
open SubexpMainAssembly (validLeaf leafCost)
open SubexpOrderedRawRecordFacts (valid_records correct)
variable {cfg : Config} {er n : ℕ} {hr : 32 ≤ workRegs er}
variable {F : SubexpOrderedRawPrefix.Formula n}

/-- Actual controller execution, conditional on the still-explicit concrete
leaf-stage provider and its invariant. The boot and record semantics are
already provided by their checked programs; the reference Boolean is never
inserted as a machine instruction. -/
noncomputable def execution (run : SubexpOrderedRawBoot.Run cfg hr F)
    (phases : Phases er (mainExtraStacks cfg))
    (hsetup : phases.setup = mainProcedure cfg er)
    (hsparsify : phases.sparsify = SubexpOrderedRawSparsify.procedure cfg hr)
    (count : ℕ) (hcount : count ≤ workStacks (mainExtraStacks cfg)) (hguard : 9 ≤ count)
    (hdecode : phases.decode = SubexpMainReady.procedure er (mainExtraStacks cfg) count hcount)
    {ell p Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hn : 0 < n)
    (invariant : MainState er (mainExtraStacks cfg) → Prop) (prefixLimit : List Bool → ℕ)
    (initial : invariant run.afterSparsify)
    (ready : ∀ base, invariant base → SubexpMainReady.StorageReady count base ∧
      base.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) = [] ∧
      base.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 10) = [])
    (provider : SubexpLeafContract.StageProvider (k := cfg.k) (Δ := Δ) (r := r) (tau := tau)
      phases count hcount hell hcap (validLeaf cfg n) invariant prefixLimit) :
    SubexpOrderedRawRuntime.Execution phases (SubexpEmptyClauseGuard.leafCallback phases) F where
  afterPrefix := run.before
  prefixSteps := run.prefixSteps
  prefixTrace := run.prefixTrace
  boot := run.boot phases hsetup hsparsify
  records := run.records
  test := SubexpLeafSemantics.test n
  cost := leafCost er count n ell p prefixLimit
  invariant := invariant
  validPayload := SubexpLeafSemantics.validPayload n (validLeaf cfg n)
  callback := SubexpLeafContract.guarded_callback_contract phases count hcount hguard hdecode
    hell hcap hn (validLeaf cfg n) invariant prefixLimit ready provider
  validRecords := valid_records run
  valid := initial
  source := run.source
  payload := run.persistent_empty 8 (by decide) (by decide)
  correct := correct run

end SubexponentialSAT.SubexpOrderedRawAssembly

end OAI.Algorithms
