import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawNodeSetupScheduleBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledCollectorBounds

namespace OAI.Algorithms

/-! The shared moment envelope applied to the same actual ordered run. -/
namespace SubexponentialSAT.SubexpOrderedRawMomentBounds
open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters SubexpComputation
open SubexpLayoutPorts (Allocation)
open SubexpMainMomentBounds (coefficient exponent degree component_sum_le)

/-- The exact phase budget is bounded using the actual setup, layout, and
collector witnesses; no additional word or execution bound is assumed. -/
theorem eventually_runtimeBound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (run : SubexpOrderedRawMomentExecution.Run boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual),
      (run.runtimeBound : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpOrderedRawNodeSetupScheduleBounds.eventually_bound
      cfg er hboot alloc hregs 1 C0 d0 hhelper,
    SubexpOrderedRawScheduledCollectorBounds.eventually_runtimeBound
      cfg er hboot alloc hregs C0 d0 hhelper] with n hs hc
  intro inst F boot base G tail hinvariant hwords valid input ready actual run
  have hsetup := hs F boot base G tail hinvariant hwords valid input ready actual
    run.initialized run.initialization
  simp only [Nat.one_mul] at hsetup
  have hcollector := hc F boot base G tail hinvariant hwords valid input ready actual
    run.initialized run.initialization
  have heq : run.runtimeBound =
      SubexpMainNodeSetupScheduleBounds.cost actual run.initialized +
        SubexpOrderedRawScheduledCollector.runtimeBound boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual run.initialized := by
    unfold SubexpOrderedRawMomentExecution.Run.runtimeBound SubexpMainNodeSetupScheduleBounds.cost
    omega
  rw [heq, Nat.cast_add]
  exact (add_le_add hsetup hcollector).trans
    (component_sum_le cfg.k d0 (SubexpOrderedRawPrefix.bitLength F) n)

/-- The same envelope applies to the measured instructions of the fixed
Main moment invocation. -/
theorem eventually_steps (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (run : SubexpOrderedRawMomentExecution.Run boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual),
      (run.steps : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [eventually_runtimeBound cfg er hboot alloc hregs C0 d0 hhelper] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual run
  exact ((Nat.cast_le (α := ℝ)).mpr run.steps_le).trans
    (hn F boot base G tail hinvariant hwords valid input ready actual run)

end SubexponentialSAT.SubexpOrderedRawMomentBounds

end OAI.Algorithms
