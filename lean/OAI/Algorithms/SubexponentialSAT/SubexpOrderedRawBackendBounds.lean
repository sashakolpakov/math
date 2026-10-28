import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBackendBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBackend
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawLayoutBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawMomentBounds
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledCRTBounds

namespace OAI.Algorithms

/-! The shared backend envelope for one actual ordered startup and leaf. -/
namespace SubexponentialSAT.SubexpOrderedRawBackendBounds
open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters SubexpComputation
open SubexpMainBackendBounds (coefficient exponent degree component_sum_le)
local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

/-- This bounds the actual prefixSteps returned by the fixed backend for
every invariant state and pending tail. No stage-cost premise remains. -/
theorem eventually_prefix (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (hsize : 672 ≤ helperSize cfg) (hregs : 16 ≤ er) (C0 d0 : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0*(SubexpOrderedRawPrefix.bitLength F+1)^d0) base),
      SubexpSetupStorage.WordBound (C0*(SubexpOrderedRawPrefix.bitLength F+1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready (SubexpMainFixedProgram.allocation cfg hsize)
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (run : SubexpOrderedRawBackend.Run (hregs := hregs) hsize boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input
          (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))),
      (run.stages.prefixSteps : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpOrderedRawLayoutBounds.eventually_bound cfg er hboot
      (SubexpMainFixedProgram.allocation cfg hsize) hregs 1 C0 d0 hsize,
    SubexpOrderedRawMomentBounds.eventually_steps cfg er hboot
      (SubexpMainFixedProgram.allocation cfg hsize) hregs C0 d0 hsize,
    SubexpOrderedRawScheduledCRTBounds.eventually_bound cfg er hboot
      (SubexpMainFixedProgram.allocation cfg hsize) hregs
      (SubexpMainFixedProgram.crtAllocation cfg hsize) 1 C0 d0 hsize] with n hl hm hc
  intro inst F boot base G tail hinvariant hwords valid input ready run
  have h1 := hl F boot base G tail hinvariant hwords valid input ready run.layout
  have h2 := hm F boot base G tail hinvariant hwords valid input ready run.layout run.moments
  have h3 := hc F boot base G tail hinvariant hwords valid input ready run.layout run.moments
  simp only [Nat.one_mul] at h1 h3
  have hp := (Nat.cast_le (α := ℝ)).mpr run.prefixBound
  push_cast at hp
  exact hp.trans ((add_le_add (add_le_add h1 h2) h3).trans
    (component_sum_le cfg.k d0 (SubexpOrderedRawPrefix.bitLength F) n))

end SubexponentialSAT.SubexpOrderedRawBackendBounds

end OAI.Algorithms
