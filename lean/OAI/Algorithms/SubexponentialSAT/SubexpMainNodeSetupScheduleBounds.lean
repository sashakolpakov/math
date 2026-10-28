import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeSetupBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutOutputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainIterationBounds

namespace OAI.Algorithms

/-!
# Scheduled cost of the actual node initialization

The layout output bound supplies every selected input word. The actual
stored dimension is identified with the schedule by the retained boot
parameters. The generated arrays contribute `2^(3*D+1)` explicitly; the
dimension estimate then charges this factor to the prescribed scale.
-/

namespace SubexponentialSAT.SubexpMainNodeSetupScheduleBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds SubexpComputation
open SubexpLayoutPorts (Allocation)

def coefficient (k : ℕ) : ℕ := 100000 * (SubexpMainLayoutBounds.constant k + 2)^4
def exponent : ℕ := 4 * (SubexpMainLayoutBounds.exponent + 1)
def degree (k d0 : ℕ) : ℕ := SubexpMainLayoutSeedBounds.degree k d0 exponent

section Finite

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
variable {ready : DyadicSchedule.Ready cfg.k cfg.T n}

noncomputable def cost
    (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)
    (initialized : MainState er (mainExtraStacks cfg)) : ℕ :=
  SubexpMainNodeSetup.runtimeBound alloc actual.out
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) +
    SubexpMainNodeScratch.runtimeBound alloc initialized + 2

/-- The polynomial factor depends on the actual layout output, derived
from its trace. The moment/slot enumeration factor is retained separately. -/
theorem seed_bound
    (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ) (ha : RelevantWordBound W a)
    {initialized : MainState er (mainExtraStacks cfg)}
    (hi : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc actual.out) initialized
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))) :
    cost actual initialized ≤ coefficient cfg.k *
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) + 1)^exponent *
      2^(3 * SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) + 1) := by
  let D := SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W D
  let c := SubexpMainLayoutBounds.constant cfg.k
  let e := SubexpMainLayoutBounds.exponent
  have hw := SubexpMainLayoutOutputBounds.seed_output_bound actual valid W ha
  have hs := SubexpMainNodeSetupBounds.setup_scratch_le_two_pow
    alloc actual.out initialized hw hi
  have hD : D ≤ X := by dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hp : (X + 1)^e ≤ (X + 1)^(e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hx : X + 1 ≤ (X + 1)^(e + 1) := Nat.le_self_pow (by omega) _
  have hsize : (c + 1) * (X + 1)^e + D + 1 ≤ (c + 2) * (X + 1)^(e + 1) := by
    have hm := Nat.mul_le_mul_left (c + 1) hp
    nlinarith only [hm, hD, hx]
  have hpoly := Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hsize 4)
  have heq : 100000 * ((c + 2) * (X + 1)^(e + 1))^4 =
      coefficient cfg.k * (X + 1)^exponent := by
    rw [mul_pow, ← pow_mul, show (e + 1) * 4 = 4 * (e + 1) by omega]
    change 100000 * ((c + 2)^4 * (X + 1)^(4 * (e + 1))) =
      (100000 * (c + 2)^4) * (X + 1)^(4 * (e + 1))
    exact (Nat.mul_assoc _ _ _).symm
  rw [heq] at hpoly
  exact hs.trans (Nat.mul_le_mul_right (2^(3 * D + 1)) hpoly)

end Finite

theorem dimension_factor {n : ℕ} (hn : GoodInput n) :
    ((2^(3 * D n + 1) : ℕ) : ℝ) ≤ 2 * (2 : ℝ)^(198 * scale n) := by
  have hd := SubexpMainIterationBounds.dimension_le_scale hn
  have hp : (2 : ℝ)^(3 * (D n : ℝ)) ≤ (2 : ℝ)^(198 * scale n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ, ← Real.rpow_natCast,
    Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hm

/-- All constants precede the input, boot, leaf, execution and initialized
state. Both selected storage and the scheduled dimension are derived from
the actual entry invariant; neither is a new promise about the worker. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (factor C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool),
      SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0 * (Encoding.formulaBitLength F + 1)^d0) base →
      SubexpSetupStorage.WordBound (C0 * (Encoding.formulaBitLength F + 1)^d0) boot.afterSetup →
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
        runtimeBound 2 199 (degree cfg.k d0) (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (factor * coefficient cfg.k) exponent C0 d0,
    eventually_goodInput] with n hn hgood
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized hi
  let L := Encoding.formulaBitLength F
  let W := C0 * (L + 1)^d0 + (8 * cfg.k + 5) * (L + 1)^(2 * cfg.k + 1)
  let d := SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
    (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))))
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W d
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpMainLayoutInitialBounds.transferred_leaf_bound boot hwords hhelper base hinvariant
      tail G valid hnL
  have hs := Nat.mul_le_mul_left factor (seed_bound actual valid W hw hi)
  have hs' : factor * cost actual initialized ≤
      ((factor * coefficient cfg.k) * (X + 1)^exponent) * 2^(3 * d + 1) := by
    simpa only [Nat.mul_assoc] using hs
  have hp : (((factor * coefficient cfg.k) * (X + 1)^exponent : ℕ) : ℝ) ≤
      runtimeBound 1 1 (degree cfg.k d0) L n :=
    hn L d W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl
  have hd : d = D n :=
    SubexpMainParameterValues.sourceInputs_dimension alloc boot
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

end SubexponentialSAT.SubexpMainNodeSetupScheduleBounds

end OAI.Algorithms
