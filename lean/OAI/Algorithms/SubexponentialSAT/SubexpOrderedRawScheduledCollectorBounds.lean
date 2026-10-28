import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledCollector
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledNodeInputBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainScheduledCollectorBounds

namespace OAI.Algorithms

/-!
# Actual ordered-input collector runtime

The boot witness and input length belong to the ordered raw encoding.
The shared physical layout state and its actual initializer feed the
existing node-size and worker estimates. No canonical-input execution is
constructed or identified with this run. Constants precede the raw input,
pending tail, and every execution witness.
-/

namespace SubexponentialSAT.SubexpOrderedRawScheduledCollectorBounds

open Filter BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters SubexpMainScheduledLayout
open SubexpMainInvariant (Stored Invariant)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

noncomputable abbrev workerCoefficient : ℝ := SubexpMainScheduledCollectorBounds.workerCoefficient
noncomputable abbrev coefficient : ℝ := SubexpMainScheduledCollectorBounds.coefficient
abbrev exponent : ℝ := SubexpMainScheduledCollectorBounds.exponent
abbrev workerDegree (k d0 : ℕ) : ℕ := SubexpMainScheduledCollectorBounds.workerDegree k d0
abbrev degree (k d0 : ℕ) : ℕ := SubexpMainScheduledCollectorBounds.degree k d0

theorem coefficient_pos : 0 < coefficient := SubexpMainScheduledCollectorBounds.coefficient_pos
theorem exponent_pos : 0 < exponent := SubexpMainScheduledCollectorBounds.exponent_pos
theorem degree_pos (k d0 : ℕ) : 0 < degree k d0 :=
  SubexpMainScheduledCollectorBounds.degree_pos k d0

private theorem overhead_le {D B L : ℕ} (hD : D ≤ L) (hB : B ≤ (L + 1)^2) :
    33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38 ≤ 202*(L + 1)^3 := by
  have hp : (L + 1)^2 ≤ (L + 1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB3 := hB.trans hp
  have hDB : D * B ≤ (L + 1)^3 := by
    calc
      D * B ≤ (L + 1) * (L + 1)^2 := Nat.mul_le_mul (by omega) hB
      _ = (L + 1)^3 := by ring
  have h1 : 1 ≤ (L + 1)^3 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [hB3, hDB, h1]

/-- The exact collector expression from the native loop, after one worker
bound and elementary bounds on the node count and scalar word width. -/
private theorem collector_bound {Q D B W L n d : ℕ} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hQ : Q ≤ (L + 1)^4)
    (hD : D ≤ L) (hB : B ≤ (L + 1)^2)
    (hW : (W : ℝ) ≤ SubexpComputation.runtimeBound C A d L n) :
    ((22 + Q*(W + 33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38) : ℕ) : ℝ) ≤
      SubexpComputation.runtimeBound (C + 224) A (d + 7) L n := by
  let X : ℝ := (L : ℝ) + 1
  let E : ℝ := (2 : ℝ)^(A * SubexpComputation.scale n)
  have hX : 1 ≤ X := by
    dsimp [X]
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hE : 1 ≤ E :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg hA (SubexpComputation.scale_nonneg n))
  have hpow (a b : ℕ) (hab : a ≤ b) : X^a ≤ X^b := by
    dsimp [X]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ L + 1) hab)
  have hW' : (W : ℝ) ≤ C*X^(d + 3)*E := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpow d (d + 3) (by omega)) hC) (by positivity : 0 ≤ E)
    exact hW.trans h
  have ho : ((33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38 : ℕ) : ℝ) ≤
      202*X^(d + 3)*E := by
    have hh : ((33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38 : ℕ) : ℝ) ≤
        202*X^3 := by
      dsimp [X]
      exact_mod_cast overhead_le hD hB
    calc
      _ ≤ 202*X^3 := hh
      _ ≤ 202*X^(d + 3) := mul_le_mul_of_nonneg_left (hpow 3 (d + 3) (by omega)) (by norm_num)
      _ ≤ 202*X^(d + 3)*E := le_mul_of_one_le_right (by positivity) hE
  have hsum : ((W + 33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38 : ℕ) : ℝ) ≤
      (C + 202)*X^(d + 3)*E := by
    push_cast at ho ⊢
    nlinarith only [hW', ho]
  have hQ' : (Q : ℝ) ≤ X^4 := by dsimp [X]; exact_mod_cast hQ
  have hbig : 1 ≤ X^(d + 7)*E :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX) hE
  calc
    _ = 22 + (Q : ℝ)*((W + 33*(4*B) + 6*(D*(4*B)) + 2*(4*B) + 38 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 22 + X^4*((C + 202)*X^(d + 3)*E) := by
      have hmul := mul_le_mul hQ' hsum (Nat.cast_nonneg _) (by positivity)
      linarith
    _ = 22 + (C + 202)*X^(d + 7)*E := by
      rw [show d + 7 = 4 + (d + 3) by omega, pow_add]
      ring
    _ ≤ (C + 224)*X^(d + 7)*E := by nlinarith only [hbig]
    _ = SubexpComputation.runtimeBound (C + 224) A (d + 7) L n := rfl

section Actual

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
  {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
  {a : MainState er (mainExtraStacks cfg)}
  (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
  (ready : DyadicSchedule.Ready cfg.k cfg.T n)
  {G : SubexpLeafData.Leaf n}
  (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
  [NeZero (r n)] (actual : Run alloc hregs a G input ready)

/-- The maximum used by the actual collector is bounded by the scheduled
envelope. The physical dimension is recovered from the same stored boot. -/
theorem iterationMax_le :
    (SubexpOrderedRawScheduledCollector.iterationMax boot initial ready input actual : ℝ) ≤
      SubexpMainIterationBounds.iterationEnvelope n := by
  change (SubexpMainWorkerScheduleBounds.maxIterations (fun i =>
    (SubexpOrderedRawScheduledEnumeration.numeric boot initial ready input actual i).iterationCount) : ℝ) ≤ _
  apply SubexpMainWorkerScheduleBounds.maxIterations_le_envelope
  intro i
  have h := (SubexpOrderedRawScheduledEnumeration.numeric boot initial ready input actual i).iterationCount_bound
  have hd := SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial
  simpa only [SubexpMainIterationBounds.iterationEnvelope, DyadicSchedule.tau,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Fintype.card_fin, hd] using h

theorem inputSize_eq (initialized : MainState er (mainExtraStacks cfg)) :
    SubexpMainNodeExecution.inputSize
      (DyadicSchedule.parameters cfg.k cfg.T cfg.width_ge_two n (DyadicSchedule.ready_goodInput ready))
      actual.result initialized = SubexpScheduledNodeInputBounds.nodeInputSize actual initialized := rfl

theorem workerBound_eq (initialized : MainState er (mainExtraStacks cfg)) :
    SubexpOrderedRawScheduledCollector.workerBound boot initial ready input actual initialized =
      SubexpNodeWorkerMasterBound.coefficient *
        (SubexpScheduledNodeInputBounds.nodeInputSize actual initialized)^3072 *
        2^(128*D n) * (SubexpOrderedRawScheduledCollector.iterationMax boot initial ready input actual + 1)^8 := by
  rw [SubexpOrderedRawScheduledCollector.workerBound,
    inputSize_eq ready input actual initialized,
    SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]

end Actual

/-- No storage-size or worker-time premise remains: both are supplied by
the actual input/layout/initializer and the checked finite worker. -/
theorem eventually_runtimeBound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (initialized : MainState er (mainExtraStacks cfg))
        (_hi : SubexpMainNodeInitialization.Result alloc
          (SubexpMainNodeSetup.prepared alloc actual.out) initialized
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
            (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))))),
      (SubexpOrderedRawScheduledCollector.runtimeBound boot
        (SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail _)
        ready input actual initialized : ℝ) ≤
          SubexpComputation.runtimeBound coefficient exponent (degree cfg.k d0)
            (SubexpOrderedRawPrefix.bitLength F) n := by
  filter_upwards [SubexpOrderedRawScheduledNodeInputBounds.eventually_bound cfg er hboot alloc hregs C0 d0 hhelper,
    SubexpMainWorkerScheduleBounds.eventually_steps_bound
      SubexpNodeWorkerMasterBound.coefficient 1 1
      (SubexpScheduledNodeInputBounds.degree cfg.k d0) (by norm_num)] with n hs hw
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized hi
  let initial := SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
    (ExecQuantitativeSparsify.encodeRawFormula G)
  let L := SubexpOrderedRawPrefix.bitLength F
  let W := SubexpOrderedRawScheduledCollector.workerBound boot initial ready input actual initialized
  have hsize := hs F boot base G tail hinvariant hwords valid input ready actual initialized hi
  have hmax := iterationMax_le boot initial ready input actual
  have hW : (W : ℝ) ≤ SubexpComputation.runtimeBound workerCoefficient exponent
      (workerDegree cfg.k d0) L n := by
    have hh := hw L (SubexpScheduledNodeInputBounds.nodeInputSize actual initialized)
      (SubexpOrderedRawScheduledCollector.iterationMax boot initial ready input actual) W
      (workerBound_eq boot initial ready input actual initialized).le hsize hmax
    simpa only [workerCoefficient, exponent, workerDegree,
      SubexpMainScheduledCollectorBounds.workerCoefficient,
      SubexpMainScheduledCollectorBounds.exponent,
      SubexpMainScheduledCollectorBounds.workerDegree, one_pow, mul_one,
      show (3072 : ℝ) + 8648 = 11720 by norm_num] using hh
  have hnL : n ≤ L := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have good := DyadicSchedule.ready_goodInput ready
  have hp : p n ≤ L := (DyadicParameterBounds.p_le_n good).trans hnL
  have hd : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))) ≤ L := by
    rw [SubexpOrderedRawParameterValues.sourceInputs_dimension alloc boot initial]
    exact (DyadicParameterBounds.D_le_n good).trans hnL
  have hQ : (p n)^4 - 1 ≤ (L + 1)^4 :=
    (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (hp.trans (Nat.le_succ L)) 4)
  have hB := SubexpMainCacheBounds.baseWidth_le_square hp hd
  have hb := collector_bound (C := workerCoefficient) (A := exponent)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256)
      (Nat.cast_nonneg SubexpNodeWorkerMasterBound.coefficient))
    SubexpMainScheduledCollectorBounds.exponent_pos.le hQ hd hB hW
  exact hb

/-- The same scheduled bound holds for a real trace with the exact
collector outputs and protected-bank frame. -/
theorem eventually_program_runs (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SubexpOrderedRawPrefix.Formula n)
      (boot : SubexpOrderedRawBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool)
      (hinvariant : Invariant cfg boot.setupOutput
        (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) base),
      SubexpSetupStorage.WordBound (C0 * (SubexpOrderedRawPrefix.bitLength F + 1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready)
        (initialized : MainState er (mainExtraStacks cfg))
        (_hi : SubexpMainNodeInitialization.Result alloc
          (SubexpMainNodeSetup.prepared alloc actual.out) initialized
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
            (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))))),
      let initial := SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
        (ExecQuantitativeSparsify.encodeRawFormula G)
      let start := SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)
      let dim := SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
        (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))))
      ∃ (out : State 16 352) (steps : ℕ),
        Trace SubexpNodeConcretePipeline.program steps
          (start.withPC (some SubexpNodeConcretePipeline.program.entry)) (out.withPC none) ∧
        (steps : ℝ) ≤ SubexpComputation.runtimeBound coefficient exponent (degree cfg.k d0)
          (SubexpOrderedRawPrefix.bitLength F) n ∧
        SubexpNodeWideLoop.Ready (SubexpNodeWorkspace.Ready (SubexpMainMomentData.store alloc initialized)) out ∧
        out.stacks 288 = (List.ofFn (SubexpNodeIndexSemantics.thetaWord (p n) dim)).flatten ∧
        out.stacks 297 = (List.ofFn (SubexpOrderedRawScheduledCollector.jet boot initial ready input actual)).flatten ∧
        out.stacks 332 = start.stacks 332 ∧
        out.stacks 333 = [] ∧ out.stacks 334 = [] ∧ out.stacks 335 = [] ∧ out.stacks 336 = [] ∧
        (∀ j : Fin 288, SubexpNodeWideLoop.ProtectedBank j →
          out.stacks (SubexpNodeWideLoop.localPorts j) = start.stacks (SubexpNodeWideLoop.localPorts j)) := by
  filter_upwards [eventually_runtimeBound cfg er hboot alloc hregs C0 d0 hhelper] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual initialized _hi
  let initial := SubexpMainInvariant.stored_transferred_input base hinvariant.toStored tail
    (ExecQuantitativeSparsify.encodeRawFormula G)
  have hb := hn F boot base G tail hinvariant hwords valid input ready actual initialized _hi
  obtain ⟨out, ⟨steps, hs, ht⟩, hout⟩ :=
    SubexpOrderedRawScheduledCollector.program_runs boot initial ready input actual _hi
  exact ⟨out, steps, ht, (Nat.cast_le (α := ℝ)).mpr hs |>.trans hb, hout⟩

end SubexponentialSAT.SubexpOrderedRawScheduledCollectorBounds


end OAI.Algorithms
