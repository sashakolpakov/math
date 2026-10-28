import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutTrace
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPackingBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledLayout

namespace OAI.Algorithms

/-!
# Selected-word growth along the actual layout execution

The six costs below group the existing source-program budgets. Every
propagation step uses the actual trace to the same state occurring in the
next cost. No closed numerical bound or bound on the pending leaf stream
is assumed.
-/

noncomputable section

namespace SubexponentialSAT.SubexpMainLayoutTraceBounds

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation)
open SubexpMainLayoutWordBounds
open SubexpMainLayoutPackingBounds (prePacking)

structure SixCosts where
  prefixCost : ℕ
  coefficientCost : ℕ
  packingCost : ℕ
  localBasisCost : ℕ
  cacheCost : ℕ
  rowCost : ℕ

/-- The prefix already includes its two composition steps. -/
def SixCosts.total (c : SixCosts) : ℕ :=
  c.prefixCost + c.coefficientCost + c.packingCost + c.localBasisCost +
    c.cacheCost + c.rowCost + 8

section Trace

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
variable {alloc : Allocation es} {hregs : 16 ≤ er}
variable {a factorState assignmentState start coefficientState packingState middle out : MainState er es}
variable {hr : 0 < r} {hQ : 0 < p^4 - 1} {scopes : List (List ℕ)}
variable {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
variable {tables : List (List Bool)}
variable {result : SubexpMainLayoutExecution.Result hregs alloc a middle out
  p r Δ R D hr hQ scopes hd tables}
variable {factorBudget : ℕ}
variable (trace : SubexpMainLayoutTrace.StageTrace alloc hregs a factorState assignmentState
  start coefficientState packingState middle out result factorBudget)

/-- Actual budgets evaluated at the actual stage endpoints. -/
def costs (_trace : SubexpMainLayoutTrace.StageTrace alloc hregs a factorState assignmentState
    start coefficientState packingState middle out result factorBudget) : SixCosts where
  prefixCost := factorBudget +
    SubexpMainAssignment.runtimeBound alloc factorState r (p^4 - 1) Δ D scopes +
    SubexpMainUniversalTypes.runtimeBound alloc assignmentState r (p^4 - 1) Δ + 2
  coefficientCost := SubexpCoefficientProgram.budget p r (p^4 - 1) R
      (SubexpMainLayoutChoices.selectedSize alloc start) +
    SubexpMainScalarAlphabet.runtimeBound alloc coefficientState p +
    SubexpMainScalarFrameWidth.runtimeBound alloc
      (SubexpMainScalarAlphabet.installed alloc coefficientState p)
  packingCost := SubexpMainPacking.runtimeBound alloc (prePacking alloc coefficientState p)
    result.choices.packing
  localBasisCost := SubexpMainLocalBasis.executionBound (Δ := Δ) alloc hregs packingState p hr hQ
    (List.ofFn result.choices.coefficients) (CoefficientSearchSemantics.alphabet p)
  cacheCost := SubexpMainCacheSetup.runtimeBound alloc middle result.rows.firstCache
      result.rows.secondCache p result.choices.packing.params.D +
    SubexpMainLagrangeCache.runtimeBound alloc result.rows.afterCache
  rowCost := SubexpMainRows.runtimeBound result.rows.cacheFacts.source
    (List.ofFn result.choices.coefficients) result.rows.cacheFacts.inverse
    result.rows.cacheFacts.negative result.rows.cacheFacts.difference
    result.choices.packing.packing scopes hd hregs alloc result.rows.afterLagrange (D + 1)

/-- The original native bound before regrouping its additions. -/
def nativeBound : ℕ :=
  (costs trace).prefixCost +
    SubexpMainLayoutChoices.tailBound alloc hregs a start coefficientState packingState middle
      result.choices +
    SubexpMainLayoutRows.runtimeBound (List.ofFn result.choices.coefficients)
      result.choices.packing.packing scopes hd result.rows + 2

theorem nativeBound_eq_total : nativeBound trace = (costs trace).total := by
  change (costs trace).prefixCost +
    ((costs trace).coefficientCost + (costs trace).packingCost + (costs trace).localBasisCost + 4) +
    ((costs trace).cacheCost + (costs trace).rowCost + 2) + 2 = _
  unfold SixCosts.total
  omega

include trace in
theorem factor_growth {W : ℕ} (ha : RelevantWordBound W a) :
    RelevantWordBound (W + factorBudget) factorState :=
  after_run ha trace.choices.factorRun

include trace in
theorem assignment_growth {W : ℕ} (ha : RelevantWordBound W factorState) :
    RelevantWordBound
      (W + SubexpMainAssignment.runtimeBound alloc factorState r (p^4 - 1) Δ D scopes)
      assignmentState :=
  after_run ha trace.choices.assignmentRun

theorem prefix_growth {W : ℕ} (ha : RelevantWordBound W a) :
    RelevantWordBound (W + (costs trace).prefixCost) start := by
  have hf := factor_growth trace ha
  have hs := assignment_growth trace hf
  have ht := after_run hs trace.choices.universalRun
  exact mono ht (by dsimp only [costs]; omega)

theorem coefficient_growth {W : ℕ} (ha : RelevantWordBound W start) :
    RelevantWordBound (W + (costs trace).coefficientCost)
      (prePacking alloc coefficientState p) := by
  have hc := after_run ha trace.choices.tailTrace.coefficientRun
  have hs := after_run hc trace.choices.tailTrace.scalarRun
  have hw := after_run hs trace.choices.tailTrace.widthRun
  simpa only [costs, prePacking, Nat.add_assoc] using hw

theorem packing_growth {W : ℕ}
    (ha : RelevantWordBound W (prePacking alloc coefficientState p)) :
    RelevantWordBound (W + (costs trace).packingCost) packingState :=
  after_run ha trace.choices.tailTrace.packingRun

theorem localBasis_growth {W : ℕ} (ha : RelevantWordBound W packingState) :
    RelevantWordBound (W + (costs trace).localBasisCost) middle :=
  after_run ha trace.choices.tailTrace.localRun

theorem cache_growth {W : ℕ} (ha : RelevantWordBound W middle) :
    RelevantWordBound (W + (costs trace).cacheCost) result.rows.afterLagrange := by
  have hc := after_run ha trace.rows.cacheRun
  have hl := after_run hc trace.rows.lagrangeRun
  simpa only [costs, Nat.add_assoc] using hl

theorem rows_growth {W : ℕ} (ha : RelevantWordBound W result.rows.afterLagrange) :
    RelevantWordBound (W + (costs trace).rowCost) out :=
  after_run ha trace.rows.rowsRun

/-- Cumulative bounds at exactly the cost boundaries of the six chunks. -/
structure IntermediateBounds (W : ℕ) : Prop where
  factor : RelevantWordBound (W + factorBudget) factorState
  assignment : RelevantWordBound
    (W + factorBudget + SubexpMainAssignment.runtimeBound alloc factorState r (p^4 - 1) Δ D scopes)
    assignmentState
  startBound : RelevantWordBound (W + (costs trace).prefixCost) start
  prePackingBound : RelevantWordBound
    (W + (costs trace).prefixCost + (costs trace).coefficientCost)
    (prePacking alloc coefficientState p)
  packingBound : RelevantWordBound
    (W + (costs trace).prefixCost + (costs trace).coefficientCost + (costs trace).packingCost)
    packingState
  middleBound : RelevantWordBound
    (W + (costs trace).prefixCost + (costs trace).coefficientCost + (costs trace).packingCost +
      (costs trace).localBasisCost) middle
  lagrangeBound : RelevantWordBound
    (W + (costs trace).prefixCost + (costs trace).coefficientCost + (costs trace).packingCost +
      (costs trace).localBasisCost + (costs trace).cacheCost) result.rows.afterLagrange
  outBound : RelevantWordBound
    (W + (costs trace).prefixCost + (costs trace).coefficientCost + (costs trace).packingCost +
      (costs trace).localBasisCost + (costs trace).cacheCost + (costs trace).rowCost) out

theorem intermediate_bounds {W : ℕ} (ha : RelevantWordBound W a) : IntermediateBounds trace W := by
  have hf := factor_growth trace ha
  have hs := assignment_growth trace hf
  have ht := prefix_growth trace ha
  have hc := coefficient_growth trace ht
  have hp := packing_growth trace hc
  have hl := localBasis_growth trace hp
  have hcache := cache_growth trace hl
  have hout := rows_growth trace hcache
  exact ⟨hf, hs, ht, hc, hp, hl, hcache, hout⟩

theorem final_growth {W : ℕ} (ha : RelevantWordBound W a) :
    RelevantWordBound (W + (costs trace).total) out := by
  exact mono (intermediate_bounds trace ha).outBound (by unfold SixCosts.total; omega)

end Trace

section Scheduled

open SubexpPackingParameters SubexpSetupProgram

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
variable {ready : DyadicSchedule.Ready cfg.k cfg.T n}
variable (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)

def runCosts : SixCosts := costs actual.stages

/-- The native run's bound is the same sum of six costs and eight steps. -/
theorem run_steps_le : actual.steps ≤ (runCosts actual).total := by
  calc
    actual.steps ≤ nativeBound actual.stages := actual.bound
    _ = (runCosts actual).total := nativeBound_eq_total actual.stages

theorem run_intermediate_bounds {W : ℕ} (ha : RelevantWordBound W a) :
    IntermediateBounds actual.stages W :=
  intermediate_bounds actual.stages ha

theorem run_final_growth {W : ℕ} (ha : RelevantWordBound W a) :
    RelevantWordBound (W + (runCosts actual).total) actual.out :=
  final_growth actual.stages ha

end Scheduled

end SubexponentialSAT.SubexpMainLayoutTraceBounds

end

end OAI.Algorithms
