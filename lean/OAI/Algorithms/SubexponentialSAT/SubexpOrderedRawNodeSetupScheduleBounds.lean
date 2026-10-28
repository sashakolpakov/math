import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeSetupScheduleBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawLayoutInitialBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawParameterValues

namespace OAI.Algorithms

/-!
# Node initialization after the actual ordered-raw layout

The native finite setup bound and its generated-array factor are reused
on the same physical layout run. Input lengths and retained parameter
values come from the ordered-raw boot; no canonical boot or run is
substituted. The pending leaf stream has no size premise.
-/

namespace SubexponentialSAT.SubexpOrderedRawNodeSetupScheduleBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds SubexpComputation
open SubexpMainNodeSetupScheduleBounds (cost coefficient exponent degree seed_bound dimension_factor)
open SubexpLayoutPorts (Allocation)

/-- Constants precede the ordered input and all actual intermediate states.
The selected layout output size and scheduled dimension are derived from
the raw boot's entry invariant and the physical layout execution. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (factor C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool),
      SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base →
      SubexpSetupStorage.WordBound (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
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
      ((factor * cost actual initialized : ℕ) : ℝ) ≤
        runtimeBound 2 199 (degree cfg.k d0) (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (factor * coefficient cfg.k) exponent C0 d0,
    eventually_goodInput] with n hn hgood
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized hi
  let L := SubexpOrderedRawPrefix.bitLength F
  let W := C0 * (L + 1)^d0 + (8 * cfg.k + 5) * (L + 1)^(2 * cfg.k + 1)
  let d := SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
    (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))))
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W d
  have hnL : n ≤ L := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpOrderedRawLayoutInitialBounds.transferred_leaf_bound
      boot hwords hhelper base hinvariant tail G valid hnL
  have hs := Nat.mul_le_mul_left factor (seed_bound actual valid W hw hi)
  have hs' : factor * cost actual initialized ≤
      ((factor * coefficient cfg.k) * (X + 1)^exponent) * 2^(3 * d + 1) := by
    simpa only [Nat.mul_assoc] using hs
  have hp : (((factor * coefficient cfg.k) * (X + 1)^exponent : ℕ) : ℝ) ≤
      runtimeBound 1 1 (degree cfg.k d0) L n :=
    hn L d W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl
  have hd : d = D n :=
    SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot
      (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail _)
  have he : ((2^(3 * d + 1) : ℕ) : ℝ) ≤ 2 * (2 : ℝ)^(198 * scale n) := by
    rw [hd]
    exact dimension_factor hgood
  have hprod := mul_le_mul hp he (Nat.cast_nonneg (2^(3 * d + 1)))
    (runtimeBound_nonneg (by norm_num : (0 : ℝ) ≤ 1) 1 (degree cfg.k d0) L n)
  calc
    ((factor * cost actual initialized : ℕ) : ℝ)
        ≤ (((factor * coefficient cfg.k) * (X + 1)^exponent : ℕ) : ℝ) *
          ((2^(3 * d + 1) : ℕ) : ℝ) := by exact_mod_cast hs'
    _ ≤ runtimeBound 1 1 (degree cfg.k d0) L n * (2 * (2 : ℝ)^(198 * scale n)) := hprod
    _ = runtimeBound 2 199 (degree cfg.k d0) L n := by
      unfold runtimeBound
      rw [one_mul, one_mul]
      calc
        _ = 2 * ((L : ℝ) + 1)^(degree cfg.k d0) *
            ((2 : ℝ)^(scale n) * (2 : ℝ)^(198 * scale n)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          ring

end SubexponentialSAT.SubexpOrderedRawNodeSetupScheduleBounds

end OAI.Algorithms
