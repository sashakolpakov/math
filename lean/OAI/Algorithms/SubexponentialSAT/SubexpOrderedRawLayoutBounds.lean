import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutOutputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawLayoutInitialBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledLayout

namespace OAI.Algorithms

/-! The complete layout runtime for the actual ordered-raw route.

The finite layout program and its six-stage cost proof are unchanged.
Only the selected input-word certificate is specialized to the ordered
boot. The input-length polynomial uses the original ordered encoding.
-/

namespace SubexponentialSAT.SubexpOrderedRawLayoutBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation)

/-- All constants precede the ordered formula, its actual boot, the leaf,
the pending stream and every intermediate layout state. A fixed multiplier
may account for the primitive compiler. No canonical boot identity or
intermediate-size premise is required. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (factor C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool),
      SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0*(SubexpOrderedRawPrefix.bitLength F+1)^d0) base →
      SubexpSetupStorage.WordBound (C0*(SubexpOrderedRawPrefix.bitLength F+1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready),
      ((factor*actual.steps : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound 1 1
          (SubexpMainLayoutSeedBounds.degree cfg.k d0 SubexpMainLayoutBounds.exponent)
          (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (factor*SubexpMainLayoutBounds.constant cfg.k)
      SubexpMainLayoutBounds.exponent C0 d0] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual
  let L := SubexpOrderedRawPrefix.bitLength F
  let W := C0*(L+1)^d0+(8*cfg.k+5)*(L+1)^(2*cfg.k+1)
  have hnL : n ≤ L := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpOrderedRawLayoutInitialBounds.transferred_leaf_bound
      boot hwords hhelper base hinvariant tail G valid hnL
  have hs := Nat.mul_le_mul_left factor (SubexpMainLayoutBounds.seed_bound actual valid W hw)
  have hs' : factor*actual.steps ≤ (factor*SubexpMainLayoutBounds.constant cfg.k)*
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))) )+1)^
            SubexpMainLayoutBounds.exponent := by
    simpa only [Nat.mul_assoc] using hs
  exact ((Nat.cast_le (α := ℝ)).mpr hs').trans
    (hn L _ W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl)

end SubexponentialSAT.SubexpOrderedRawLayoutBounds

end OAI.Algorithms
