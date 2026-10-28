import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutChoicesTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutExecution

namespace OAI.Algorithms

/-! The complete actual layout phase preserves the loop's stored setup
parameters and threshold bytes, and regenerates caches within the same cap. -/

namespace SubexponentialSAT.SubexpMainLayoutStored

open SubexpMainProgram SubexpSetupProgram SubexpMainInvariant
open SubexpLayoutPorts (Allocation)

variable {cfg : Config} {er p r Q Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a factorState assignmentState start coefficientState packingState middle out :
  MainState er (mainExtraStacks cfg)}
variable {hr : 0 < r} {hQ : 0 < Q} {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)} {factorBudget : ℕ}
variable {setup : SetupState cfg} {B : ℕ}

theorem choices
    (result : SubexpMainLayoutChoices.Result alloc a middle p r Q Δ R D hr hQ scopes hd tables)
    (trace : SubexpMainLayoutChoicesTrace.StageTrace alloc hregs a factorState assignmentState
      start coefficientState packingState middle result factorBudget)
    (halloc : alloc.ordinaryCount = helperSize cfg) (initial : Stored cfg setup B a) :
    Stored cfg setup B middle := by
  apply stored_of_frames initial
  · intro i _
    exact result.prefixResult.persistent i
  · intro i
    have hithreshold := threshold_range cfg i
    apply trace.threshold_frame _ _ hithreshold.2
    rw [halloc]
    exact hithreshold.1
  · intro i hi
    rw [result.prefixResult.persistent]
    exact initial.caches i hi

variable {hQ4 : 0 < p^4 - 1}

theorem stored
    (result : SubexpMainLayoutExecution.Result hregs alloc a middle out p r Δ R D hr hQ4 scopes hd tables)
    (trace : SubexpMainLayoutChoicesTrace.StageTrace alloc hregs a factorState assignmentState
      start coefficientState packingState middle result.choices factorBudget)
    (halloc : alloc.ordinaryCount = helperSize cfg) (initial : Stored cfg setup B a)
    (hB : SubexpMainCacheBounds.regeneratedBound p D ≤ B) :
    Stored cfg setup B out :=
  SubexpMainLayoutInvariant.stored (List.ofFn result.choices.coefficients)
    result.choices.packing.packing scopes hd result.rows halloc
    (choices result.choices trace halloc initial) hB

/-- The parser's pending stream, payload and leaf words are particular
instances of this unchanged-persistent-word theorem. -/
theorem persistent_frame
    (result : SubexpMainLayoutExecution.Result hregs alloc a middle out p r Δ R D hr hQ4 scopes hd tables)
    (i : Fin 32) (hi : i ∉ SubexpMainCacheSetup.changedPersistent) :
    out.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) :=
  (SubexpMainLayoutRows.Result.persistent_frame (List.ofFn result.choices.coefficients)
    result.choices.packing.packing scopes hd result.rows i hi).trans
      (result.choices.prefixResult.persistent i)

end SubexponentialSAT.SubexpMainLayoutStored

end OAI.Algorithms
