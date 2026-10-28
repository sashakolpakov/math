import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeInputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutOutputBounds

namespace OAI.Algorithms

/-!
# Scheduled sizes of the actual node-worker inputs

The selected original words are bounded by the completed layout trace.
Scalar and index widths are then bounded by the same numerical seed. This
retains the layout's subexponential storage term and keeps initialization
and moment-header execution costs separate.
-/

namespace SubexponentialSAT.SubexpScheduledNodeInputBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def coefficient (k : ℕ) : ℕ := 1000 * (SubexpMainLayoutBounds.constant k + 13)
def exponent : ℕ := SubexpMainLayoutBounds.exponent + 2
def degree (k d0 : ℕ) : ℕ := SubexpMainLayoutSeedBounds.degree k d0 exponent

private theorem scale_le_pow {W p D R r X c e : ℕ}
    (hW : W ≤ (c + 1) * (X + 1)^e)
    (hp : p ≤ X) (hD : D ≤ X) (hR : R ≤ X) (hr : r ≤ X)
    (hQ : p^4 - 1 ≤ X) :
    SubexpMainNodeInputBounds.scale W p D R r ≤ (c + 13) * (X + 1)^(e + 2) := by
  let Y := (X + 1)^(e + 2)
  have hbase : X + 1 ≤ Y := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by omega : 1 ≤ X + 1) (by omega : 1 ≤ e + 2))
  have hpow : (X + 1)^2 ≤ Y :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hW' : W ≤ (c + 1) * Y := hW.trans
    (Nat.mul_le_mul_left (c + 1) (Nat.pow_le_pow_right (by omega) (by omega)))
  have hp' : p ≤ Y := hp.trans ((Nat.le_succ X).trans hbase)
  have hD' : D ≤ Y := hD.trans ((Nat.le_succ X).trans hbase)
  have hR' : R ≤ Y := hR.trans ((Nat.le_succ X).trans hbase)
  have hr' : r ≤ Y := hr.trans ((Nat.le_succ X).trans hbase)
  have hQ' : p^4 - 1 ≤ Y := hQ.trans ((Nat.le_succ X).trans hbase)
  have hB : SubexpLiftRing.baseWidth p (D + 1) ≤ Y :=
    (SubexpMainCacheBounds.baseWidth_le_square hp hD).trans hpow
  have hb : SubexpLiftRing.baseWidth p 1 ≤ Y := by
    have hlog := Nat.add_le_add_right ((Nat.log_le_self 2 p).trans hp) 1
    have hb0 : SubexpLiftRing.baseWidth p 1 ≤ X + 1 := by
      simpa only [SubexpLiftRing.baseWidth, one_mul] using hlog
    exact hb0.trans hbase
  have hI0 : SubexpSymbolicCost.indexBits D ≤ 4 * (D + 1)^2 := by
    unfold SubexpSymbolicCost.indexBits
    nlinarith
  have hI : SubexpSymbolicCost.indexBits D ≤ 4 * Y :=
    hI0.trans (Nat.mul_le_mul_left 4
      ((Nat.pow_le_pow_left (Nat.add_le_add_right hD 1) 2).trans hpow))
  have h1 : 1 ≤ Y := (Nat.succ_pos X).trans_le hbase
  change W + p + D + R + r + (p^4 - 1) + SubexpLiftRing.baseWidth p (D + 1) +
    SubexpLiftRing.baseWidth p 1 + SubexpSymbolicCost.indexBits D + 1 ≤ (c + 13) * Y
  nlinarith only [hW', hp', hD', hR', hr', hQ', hB, hb, hI, h1]

section Finite

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
variable {ready : DyadicSchedule.Ready cfg.k cfg.T n}

/-- The exact uniform input size of the initialized physical worker. -/
noncomputable def nodeInputSize
    (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)
    (initialized : MainState er (mainExtraStacks cfg)) : ℕ :=
  SubexpNodeUniformBound.uniformSize (p n)
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
    (DyadicSchedule.R cfg.k cfg.T n) (r n)
    (SubexpDenseRowTableSemantics.expressionRows
      (SubexpMainNodeArguments.rowExpr actual.result)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
      0 (SubexpMainScheduledLayout.scopes input)).length
    (SubexpMainMomentData.store alloc initialized)
    (SubexpNodeLiftData.liftedNodeWords (p n)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) + 1)
      (SubexpMainNodeArguments.source actual.result).modulus)
    (SubexpMainNodeArguments.source actual.result).modulus.bits
    (SubexpQuarticFlatNeg.flat (SubexpMainMomentData.target (p n)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))).zero)
    (SubexpQuarticFlatNeg.flat (SubexpMainMomentData.target (p n)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))).one)
    (SubexpMainScheduledLayout.scopes input) (SubexpMainScheduledLayout.tables input)
    ((SubexpMainNodeArguments.cache actual.result).map (List.map SubexpQuarticFlatNeg.flat))

/-- The word bound comes from the actual layout execution. No output-size
certificate is required from the node worker or its initializer. -/
theorem seed_bound
    (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ) (ha : RelevantWordBound W a)
    {initialized : MainState er (mainExtraStacks cfg)}
    (hi : SubexpMainNodeInitialization.Result alloc
      (SubexpMainNodeSetup.prepared alloc actual.out) initialized
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))) :
    nodeInputSize actual initialized ≤ coefficient cfg.k *
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)) + 1)^exponent := by
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
    (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
  have hw := SubexpMainLayoutOutputBounds.seed_output_bound actual valid W ha
  have hu := SubexpMainNodeInputBounds.uniformSize_le_linear actual.result hi hw
  have hp : p n ≤ X := by dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hD : SubexpLayoutConstruction.dimension
      (SubexpMainLayout.Factors.sourceInputs alloc a) ≤ X := by
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hR : DyadicSchedule.R cfg.k cfg.T n ≤ X := by
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hr : r n ≤ X := by dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hQ : (p n)^4 - 1 ≤ X := by
    change DyadicSchedule.Q n ≤ X
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hs := scale_le_pow (c := SubexpMainLayoutBounds.constant cfg.k)
    (e := SubexpMainLayoutBounds.exponent) le_rfl hp hD hR hr hQ
  apply hu.trans
  simpa only [coefficient, exponent, Nat.mul_assoc] using Nat.mul_le_mul_left 1000 hs

end Finite

/-- Fixed constants precede every varying input and every actual execution.
The pending leaf stream is unrestricted. The seed lemma absorbs both the
layout storage and the fixed width overhead into the scheduled envelope. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
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
      (nodeInputSize actual initialized : ℝ) ≤
        SubexpComputation.runtimeBound 1 1 (degree cfg.k d0) (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (coefficient cfg.k) exponent C0 d0] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized hi
  let L := Encoding.formulaBitLength F
  let W := C0 * (L + 1)^d0 + (8 * cfg.k + 5) * (L + 1)^(2 * cfg.k + 1)
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpMainLayoutInitialBounds.transferred_leaf_bound boot hwords hhelper base hinvariant
      tail G valid hnL
  have hs := seed_bound actual valid W hw hi
  exact ((Nat.cast_le (α := ℝ)).mpr hs).trans
    (hn L _ W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl)

end SubexponentialSAT.SubexpScheduledNodeInputBounds

end OAI.Algorithms
