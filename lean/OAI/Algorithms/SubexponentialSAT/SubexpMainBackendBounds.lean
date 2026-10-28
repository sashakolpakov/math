import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBackend
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledCRTBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainMeasuredBound

namespace OAI.Algorithms

/-! Uniform bound for the actual three-phase backend. Every stage bound
uses the same boot, transferred leaf, layout run, and moment run. -/

namespace SubexponentialSAT.SubexpMainBackendBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters SubexpComputation

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

noncomputable def coefficient : ℝ := 2 + SubexpMainMomentBounds.coefficient
def exponent : ℝ := SubexpMainMomentBounds.exponent + 1
def degree (k d0 : ℕ) : ℕ :=
  SubexpMainLayoutSeedBounds.degree k d0 SubexpMainLayoutBounds.exponent +
    SubexpMainMomentBounds.degree k d0 +
    SubexpMainLayoutSeedBounds.degree k d0 SubexpMainScheduledCRTBounds.exponent + 1

theorem coefficient_ge_one : 1 ≤ coefficient := by
  have h := SubexpMainMomentBounds.coefficient_pos
  unfold coefficient
  linarith

theorem exponent_ge_one : 1 ≤ exponent := by
  have h := SubexpMainMomentBounds.exponent_pos
  unfold exponent
  linarith

theorem degree_pos (k d0 : ℕ) : 0 < degree k d0 := by unfold degree; omega

theorem component_sum_le (k d0 L n : ℕ) :
    runtimeBound 1 1 (SubexpMainLayoutSeedBounds.degree k d0 SubexpMainLayoutBounds.exponent) L n +
      runtimeBound SubexpMainMomentBounds.coefficient SubexpMainMomentBounds.exponent
        (SubexpMainMomentBounds.degree k d0) L n +
      runtimeBound 1 1 (SubexpMainLayoutSeedBounds.degree k d0 SubexpMainScheduledCRTBounds.exponent) L n ≤
      runtimeBound coefficient exponent (degree k d0) L n := by
  have hl := SubexpMainMeasuredBound.monotone (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    exponent_ge_one (show SubexpMainLayoutSeedBounds.degree k d0 SubexpMainLayoutBounds.exponent ≤
      degree k d0 by unfold degree; omega) L n
  have hm := SubexpMainMeasuredBound.monotone SubexpMainMomentBounds.coefficient_pos.le le_rfl
    (show SubexpMainMomentBounds.exponent ≤ exponent by unfold exponent; linarith)
    (show SubexpMainMomentBounds.degree k d0 ≤ degree k d0 by unfold degree; omega) L n
  have hc := SubexpMainMeasuredBound.monotone (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    exponent_ge_one (show SubexpMainLayoutSeedBounds.degree k d0 SubexpMainScheduledCRTBounds.exponent ≤
      degree k d0 by unfold degree; omega) L n
  apply (add_le_add (add_le_add hl hm) hc).trans
  unfold runtimeBound coefficient
  exact le_of_eq (by ring)

/-- This bounds the actual prefixSteps returned by the fixed backend for
every invariant state and pending tail. No stage-cost premise remains. -/
theorem eventually_prefix (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (hsize : 672 ≤ helperSize cfg) (hregs : 16 ≤ er) (C0 d0 : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0*(Encoding.formulaBitLength F+1)^d0) base),
      SubexpSetupStorage.WordBound (C0*(Encoding.formulaBitLength F+1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready (SubexpMainFixedProgram.allocation cfg hsize)
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (run : SubexpMainBackend.Run (hregs := hregs) hsize boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input
          (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))),
      (run.stages.prefixSteps : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainLayoutBounds.eventually_bound cfg er hboot
      (SubexpMainFixedProgram.allocation cfg hsize) hregs 1 C0 d0 hsize,
    SubexpMainMomentBounds.eventually_steps cfg er hboot
      (SubexpMainFixedProgram.allocation cfg hsize) hregs C0 d0 hsize,
    SubexpMainScheduledCRTBounds.eventually_bound cfg er hboot
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
    (component_sum_le cfg.k d0 (Encoding.formulaBitLength F) n))

end SubexponentialSAT.SubexpMainBackendBounds

end OAI.Algorithms
