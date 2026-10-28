import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScheduledNodeInputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawLayoutBounds

namespace OAI.Algorithms

/-!
# Node input sizes after the actual ordered-raw boot

The native layout record and its boot-independent size theorem apply to
the actual ordered-raw execution directly. The initial word certificate
comes from that boot's own setup, and the polynomial uses the original
ordered input length. No canonical-input boot or execution identity is
assumed.
-/

namespace SubexponentialSAT.SubexpOrderedRawScheduledNodeInputBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation)
open SubexpScheduledNodeInputBounds (nodeInputSize coefficient exponent degree)

/-- All constants precede the ordered formula and every actual execution.
The pending stream remains unrestricted, and all node-input sizes are
derived from the physical layout and initializer results. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool),
      SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base →
      SubexpSetupStorage.WordBound
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (initialized : MainState er (mainExtraStacks cfg))
        (_hi : SubexpMainNodeInitialization.Result alloc
          (SubexpMainNodeSetup.prepared alloc actual.out) initialized
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
            (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))))),
      (nodeInputSize actual initialized : ℝ) ≤
        SubexpComputation.runtimeBound 1 1 (degree cfg.k d0)
          (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (coefficient cfg.k) exponent C0 d0] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized hi
  let L := SubexpOrderedRawPrefix.bitLength F
  let W := C0 * (L + 1)^d0 + (8 * cfg.k + 5) * (L + 1)^(2 * cfg.k + 1)
  have hnL : n ≤ L := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpOrderedRawLayoutInitialBounds.transferred_leaf_bound boot hwords hhelper base
      hinvariant tail G valid hnL
  have hs := SubexpScheduledNodeInputBounds.seed_bound actual valid W hw hi
  exact ((Nat.cast_le (α := ℝ)).mpr hs).trans
    (hn L _ W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl)

end SubexponentialSAT.SubexpOrderedRawScheduledNodeInputBounds

end OAI.Algorithms
