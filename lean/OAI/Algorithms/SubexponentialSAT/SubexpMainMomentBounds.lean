import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeSetupScheduleBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledCollectorBounds

namespace OAI.Algorithms

/-!
# Uniform bound for the complete actual moment phase

The initializer and collector bounds apply to the same initialized state
retained by `MainMomentExecution.Run`. The fixed constants precede the
formula, pending stream, leaf, and execution witnesses.
-/

namespace SubexponentialSAT.SubexpMainMomentBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpComputation
open SubexpLayoutPorts (Allocation)

noncomputable def coefficient : ℝ :=
  2 + SubexpMainScheduledCollectorBounds.coefficient

def exponent : ℝ := SubexpMainScheduledCollectorBounds.exponent

def degree (k d0 : ℕ) : ℕ :=
  max (SubexpMainNodeSetupScheduleBounds.degree k d0)
    (SubexpMainScheduledCollectorBounds.degree k d0)

theorem coefficient_pos : 0 < coefficient := by
  have h := SubexpMainScheduledCollectorBounds.coefficient_pos
  unfold coefficient
  linarith

theorem exponent_pos : 0 < exponent :=
  SubexpMainScheduledCollectorBounds.exponent_pos

theorem degree_pos (k d0 : ℕ) : 0 < degree k d0 :=
  lt_of_lt_of_le (SubexpMainScheduledCollectorBounds.degree_pos k d0) (le_max_right _ _)

private theorem degree_mono {C A : ℝ} (hC : 0 ≤ C) {d e : ℕ} (hde : d ≤ e)
    (L n : ℕ) : runtimeBound C A d L n ≤ runtimeBound C A e L n := by
  have hp : ((L : ℝ) + 1)^d ≤ ((L : ℝ) + 1)^e := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ L + 1) hde)
  unfold runtimeBound
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity)

theorem component_sum_le (k d0 L n : ℕ) :
    runtimeBound 2 199 (SubexpMainNodeSetupScheduleBounds.degree k d0) L n +
      runtimeBound SubexpMainScheduledCollectorBounds.coefficient
        SubexpMainScheduledCollectorBounds.exponent
        (SubexpMainScheduledCollectorBounds.degree k d0) L n ≤
      runtimeBound coefficient exponent (degree k d0) L n := by
  have hs := (degree_mono (A := 199) (by norm_num : (0 : ℝ) ≤ 2)
    (le_max_left (SubexpMainNodeSetupScheduleBounds.degree k d0)
      (SubexpMainScheduledCollectorBounds.degree k d0)) L n).trans
    (runtimeBound_mono_exponent (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num [exponent, SubexpMainScheduledCollectorBounds.exponent] :
        (199 : ℝ) ≤ exponent) (degree k d0) L n)
  have hc := degree_mono (A := SubexpMainScheduledCollectorBounds.exponent)
    (le_of_lt SubexpMainScheduledCollectorBounds.coefficient_pos)
    (le_max_right (SubexpMainNodeSetupScheduleBounds.degree k d0)
      (SubexpMainScheduledCollectorBounds.degree k d0)) L n
  apply (add_le_add hs hc).trans
  unfold runtimeBound coefficient exponent degree
  exact le_of_eq (by ring)

/-- The exact phase budget is bounded using the actual setup, layout, and
collector witnesses; no additional word or execution bound is assumed. -/
theorem eventually_runtimeBound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (Encoding.formulaBitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (Encoding.formulaBitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (run : SubexpMainMomentExecution.Run boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual),
      (run.runtimeBound : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainNodeSetupScheduleBounds.eventually_bound
      cfg er hboot alloc hregs 1 C0 d0 hhelper,
    SubexpMainScheduledCollectorBounds.eventually_runtimeBound
      cfg er hboot alloc hregs C0 d0 hhelper] with n hs hc
  intro inst F boot base G tail hinvariant hwords valid input ready actual run
  have hsetup := hs F boot base G tail hinvariant hwords valid input ready actual
    run.initialized run.initialization
  simp only [Nat.one_mul] at hsetup
  have hcollector := hc F boot base G tail hinvariant hwords valid input ready actual
    run.initialized run.initialization
  have heq : run.runtimeBound =
      SubexpMainNodeSetupScheduleBounds.cost actual run.initialized +
        SubexpMainScheduledCollector.runtimeBound boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual run.initialized := by
    unfold SubexpMainMomentExecution.Run.runtimeBound SubexpMainNodeSetupScheduleBounds.cost
    omega
  rw [heq, Nat.cast_add]
  exact (add_le_add hsetup hcollector).trans
    (component_sum_le cfg.k d0 (Encoding.formulaBitLength F) n)

/-- The same envelope applies to the measured instructions of the fixed
Main moment invocation. -/
theorem eventually_steps (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (Encoding.formulaBitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (Encoding.formulaBitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))
          n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (run : SubexpMainMomentExecution.Run boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual),
      (run.steps : ℝ) ≤ runtimeBound coefficient exponent (degree cfg.k d0)
        (Encoding.formulaBitLength F) n := by
  filter_upwards [eventually_runtimeBound cfg er hboot alloc hregs C0 d0 hhelper] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual run
  exact ((Nat.cast_le (α := ℝ)).mpr run.steps_le).trans
    (hn F boot base G tail hinvariant hwords valid input ready actual run)

end SubexponentialSAT.SubexpMainMomentBounds

end OAI.Algorithms
