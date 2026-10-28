import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentCRTBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutOutputBounds

namespace OAI.Algorithms

/-!
# Scheduled cost of the actual CRT readback

The input is the readback of the concrete moment run. Its two retained word
lengths come from the actual layout trace, and its empty answer word comes
from the loop invariant before the current leaf is transferred. Fixed
powers of the resulting seed are absorbed by the established schedule
estimate, uniformly in the pending stream.
-/

namespace SubexponentialSAT.SubexpMainScheduledCRTBounds

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters
open SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def coefficient (k : ℕ) : ℕ :=
  10000000000000000000 * (2 * (SubexpMainLayoutBounds.constant k + 1) + 5)^32

def exponent : ℕ := (SubexpMainLayoutBounds.exponent + 2) * 32

private theorem size_le_pow (C e X p D Q : ℕ)
    (hp : p ≤ X) (hD : D ≤ X) (hQ : Q ≤ X) :
    p + D + Q + SubexpLiftRing.baseWidth p (D+1) +
        2*((C+1)*(X+1)^e) + 1 ≤
      (2*(C+1)+5)*(X+1)^(e+2) := by
  let P := (X+1)^(e+2)
  have hXP : X+1 ≤ P := Nat.le_self_pow (by omega) _
  have h1 : 1 ≤ P := (Nat.succ_le_succ (Nat.zero_le X)).trans hXP
  have hpP : p ≤ P := hp.trans ((Nat.le_succ X).trans hXP)
  have hDP : D ≤ P := hD.trans ((Nat.le_succ X).trans hXP)
  have hQP : Q ≤ P := hQ.trans ((Nat.le_succ X).trans hXP)
  have hwidth : SubexpLiftRing.baseWidth p (D+1) ≤ P :=
    (SubexpMainCacheBounds.baseWidth_le_square hp hD).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hword : (C+1)*(X+1)^e ≤ (C+1)*P :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  change _ ≤ (2*(C+1)+5)*P
  nlinarith only [h1, hpP, hDP, hQP, hwidth, hword]

section Finite

variable {cfg : Config} {er n B : ℕ} [NeZero (r n)]
  {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
  {F : SAT.CNF (Fin n)} {alloc : Allocation (mainExtraStacks cfg)}
  {a : MainState er (mainExtraStacks cfg)}
  {boot : SubexpMainBoot.Run cfg hrBoot F}
  {initial : SubexpMainInvariant.Stored cfg boot.setupOutput B a}
  {ready : DyadicSchedule.Ready cfg.k cfg.T n} {G : SubexpLeafData.Leaf n}
  {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
  {actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready}

private abbrev physicalD :=
  SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)

/-- A fixed power of the same seed used by the actual layout program bounds
the exact readback, including its actual padded retained words. -/
theorem seed_bound (run : SubexpMainMomentExecution.Run boot initial ready input actual)
    (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ)
    (ha : RelevantWordBound W a)
    (hanswer : a.stacks (persistent (mainExtraStacks cfg) 10) = []) :
    (SubexpMainMomentExecution.Run.readback boot initial ready input actual run crtAlloc).bound ≤ coefficient cfg.k *
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (physicalD (alloc := alloc) (a := a)) + 1)^exponent := by
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
    (physicalD (alloc := alloc) (a := a))
  have hp : p n ≤ X := by dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hd : physicalD (alloc := alloc) (a := a) ≤ X := by
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hq : DyadicSchedule.Q n ≤ X := by
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]; omega
  have hw := SubexpMainLayoutOutputBounds.seed_output_bound actual valid W ha
  have hread := SubexpMainMomentCRTBounds.readback_bound_le_layout actual.result
    run.initialization run.out run.outReady hw crtAlloc hanswer
    (SubexpMainMomentExecution.Run.readback boot initial ready input actual run crtAlloc)
  change (SubexpMainMomentExecution.Run.readback boot initial ready input actual run crtAlloc).bound ≤ 10000000000000000000 *
    (p n + physicalD (alloc := alloc) (a := a) + DyadicSchedule.Q n +
      SubexpLiftRing.baseWidth (p n) (physicalD (alloc := alloc) (a := a)+1) +
      2*((SubexpMainLayoutBounds.constant cfg.k+1)*
        (X+1)^SubexpMainLayoutBounds.exponent)+1)^32 at hread
  have hb := size_le_pow (SubexpMainLayoutBounds.constant cfg.k)
    SubexpMainLayoutBounds.exponent X (p n) (physicalD (alloc := alloc) (a := a))
    (DyadicSchedule.Q n) hp hd hq
  apply hread.trans
  calc
    _ ≤ 10000000000000000000 *
        ((2*(SubexpMainLayoutBounds.constant cfg.k+1)+5)*
          (X+1)^(SubexpMainLayoutBounds.exponent+2))^32 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 32)
    _ = coefficient cfg.k * (X+1)^exponent := by
      simp only [coefficient, exponent, mul_pow, ← pow_mul, Nat.mul_assoc]

end Finite

/-- The answer word is untouched by parsing and transferring a leaf. -/
theorem transferred_answer {cfg : Config} {er B : ℕ} {setup : SetupState cfg}
    (base : MainState er (mainExtraStacks cfg))
    (h : SubexpMainInvariant.Invariant cfg setup B base) (tail bits : List Bool) :
    (transferredData (leafInput base tail bits)).stacks
      (persistent (mainExtraStacks cfg) 10) = [] := by
  apply (SubexpMainInvariant.transferred_input_stack base tail bits
    (persistent (mainExtraStacks cfg) 10) ?_ ?_ ?_).trans h.answer
  · intro he
    exact (by decide : (10 : Fin 32) ≠ 7) (persistent_injective _ he)
  · intro he
    exact (by decide : (10 : Fin 32) ≠ 8) (persistent_injective _ he)
  · intro he
    exact (by decide : (10 : Fin 32) ≠ 9) (persistent_injective _ he)

/-- All constants precede the input and the actual executions. The word
bound is the same completed setup bound used by the loop invariant; there
is no separate assumption on the layout or moment output size. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (crtAlloc : SubexpMainCRT.Allocation (mainExtraStacks cfg))
    (factor C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0*(Encoding.formulaBitLength F+1)^d0) base),
      SubexpSetupStorage.WordBound (C0*(Encoding.formulaBitLength F+1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (run : SubexpMainMomentExecution.Run boot
          (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
            (ExecQuantitativeSparsify.encodeRawFormula G)) ready input actual),
      ((factor*(SubexpMainMomentExecution.Run.readback boot _ ready input actual run crtAlloc).bound : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound 1 1
          (SubexpMainLayoutSeedBounds.degree cfg.k d0 exponent) (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (factor*coefficient cfg.k) exponent C0 d0] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual run
  let L := Encoding.formulaBitLength F
  let W := C0*(L+1)^d0+(8*cfg.k+5)*(L+1)^(2*cfg.k+1)
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpMainLayoutInitialBounds.transferred_leaf_bound boot hwords hhelper
      base hinvariant tail G valid hnL
  have hs := Nat.mul_le_mul_left factor
    (seed_bound run crtAlloc valid W hw
      (transferred_answer base hinvariant tail (ExecQuantitativeSparsify.encodeRawFormula G)))
  have hs' : factor*(SubexpMainMomentExecution.Run.readback boot _ ready input actual run crtAlloc).bound ≤ (factor*coefficient cfg.k)*
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))))+1)^exponent := by
    simpa only [Nat.mul_assoc] using hs
  exact ((Nat.cast_le (α := ℝ)).mpr hs').trans
    (hn L _ W hnL (SubexpMainLayoutBounds.physical_dimension_le (input := input)) le_rfl)

end SubexponentialSAT.SubexpMainScheduledCRTBounds

end OAI.Algorithms
