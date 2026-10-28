import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPrefixBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutMajorants
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutTraceBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutInitialBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSeedBounds

namespace OAI.Algorithms

/-!
# A bound for the complete physical Main layout phase

All six cost groups use the actual intermediate states in the recorded
execution. Selected-word bounds are propagated by real instruction traces.
The final input polynomial and local exponential bound are independent of
the pending leaf stream.
-/

namespace SubexponentialSAT.SubexpMainLayoutBounds

open Filter BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters SubexpMainLayoutWordBounds SubexpMainLayoutTraceBounds
open SubexpMainLayoutPolynomial
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

def stageConstant (k : ℕ) : ℕ :=
  SubexpMainLayoutPrefixBounds.coefficient + SubexpMainLayoutMajorants.coefficientConstant +
  SubexpMainLayoutPackingBounds.packingCoefficient + 200 + SubexpMainLayoutMajorants.cacheConstant +
  SubexpMainLayoutMajorants.rowConstant k + 1

def stageDegree : ℕ :=
  1500 + 8 + 12 + 2 + SubexpMainLayoutCacheArithmetic.polynomialDegree + 39 + 1

def constant (k : ℕ) : ℕ := coefficient (stageConstant k) stageDegree 6 + 8
def exponent : ℕ := degree stageDegree 6

private theorem cap {c C e d x y : ℕ} (hc : c ≤ C) (he : e ≤ d)
    (hxy : x ≤ y) (hy : 1 ≤ y) : c*x^e ≤ C*y^d :=
  Nat.mul_le_mul hc ((Nat.pow_le_pow_left hxy e).trans (Nat.pow_le_pow_right hy he))

private theorem advance {C d X i s t : ℕ}
    (hs : s ≤ grow C d X i) (ht : t ≤ C*(grow C d X i+X+1)^d) :
    s+t ≤ grow C d X (i+1) := by
  change s+t ≤ grow C d X i + C*(grow C d X i+X+1)^d+1
  omega

section Finite

variable {cfg : Config} {er n : ℕ} [NeZero (r n)]
variable {alloc : Allocation (mainExtraStacks cfg)} {hregs : 16 ≤ er}
variable {a : MainState er (mainExtraStacks cfg)} {G : SubexpLeafData.Leaf n}
variable {input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G}
variable {ready : DyadicSchedule.Ready cfg.k cfg.T n}
variable (actual : SubexpMainScheduledLayout.Run alloc hregs a G input ready)

private abbrev physicalD :=
  SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)

theorem finite_bound (valid : SubexpMainAssembly.validLeaf cfg n G) (W X : ℕ)
    (ha : RelevantWordBound W a) (hWX : W ≤ X)
    (hprefix : SubexpMainLayoutPrefixBounds.size W n cfg.k cfg.T ≤ X)
    (hp : p n ≤ X) (hr : r n ≤ X) (hQ : DyadicSchedule.Q n ≤ X)
    (hδ : DyadicSchedule.delta cfg.k cfg.T n ≤ X) (hR : DyadicSchedule.R cfg.k cfg.T n ≤ X)
    (hD : physicalD (alloc := alloc) (a := a) ≤ X)
    (hpower : (p n)^(DyadicSchedule.R cfg.k cfg.T n) ≤ X)
    (hnative : Subexp.LocalBasisBatchProgram.sourceBudget (Δ := DyadicSchedule.delta cfg.k cfg.T n)
      (p n) (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) (DyadicSchedule.Q_pos n)
      (List.ofFn actual.result.choices.coefficients)
      (Subexp.CoefficientSearchSemantics.alphabet (p n)) ≤ X) :
    actual.steps ≤ constant cfg.k * (X+1)^exponent := by
  let C := stageConstant cfg.k
  let d := stageDegree
  let g := grow C d X
  let cs := runCosts actual
  have hc : SubexpMainLayoutPrefixBounds.coefficient ≤ C ∧
      SubexpMainLayoutMajorants.coefficientConstant ≤ C ∧
      SubexpMainLayoutPackingBounds.packingCoefficient ≤ C ∧ 200 ≤ C ∧
      SubexpMainLayoutMajorants.cacheConstant ≤ C ∧ SubexpMainLayoutMajorants.rowConstant cfg.k ≤ C := by
    dsimp only [C, stageConstant]
    omega
  have hd : 1500 ≤ d ∧ 8 ≤ d ∧ 12 ≤ d ∧ 2 ≤ d ∧
      SubexpMainLayoutCacheArithmetic.polynomialDegree ≤ d ∧ 39 ≤ d := by
    dsimp only [d, stageDegree]
    omega
  have hg (i : ℕ) : X ≤ g i := self_le_grow C d X i
  have hpre := SubexpMainLayoutPrefixBounds.runtimeBound_le input ready actual valid W ha
  have h0 : cs.prefixCost ≤ C*(g 0+X+1)^d := by
    apply hpre.trans
    exact cap hc.1 hd.1 (by dsimp only [g, grow]; omega) (by omega)
  have s0 : W ≤ g 0 := hWX
  have s1 : W+cs.prefixCost ≤ g 1 := advance s0 h0
  have hm := run_intermediate_bounds actual ha
  have hw1 : RelevantWordBound (g 1) actual.start := mono hm.startBound s1
  obtain ⟨hcoef, hcoefEq⟩ := actual.stages.choices.tailTrace.coefficientResult
  have hco := SubexpMainLayoutCoefficientBounds.three_stage_budget_le alloc hw1 hcoef
  have h1 : cs.coefficientCost ≤ C*(g 1+X+1)^d := by
    apply hco.trans
    apply (SubexpMainLayoutMajorants.coefficient_bound (g 1) X (p n)
      (DyadicSchedule.Q n) (DyadicSchedule.R cfg.k cfg.T n) hp hQ hR hpower).trans
    exact cap hc.2.1 hd.2.1 le_rfl (by omega)
  have s2 : W+cs.prefixCost+cs.coefficientCost ≤ g 2 := advance s1 h1
  have hw2 : RelevantWordBound (g 2)
      (SubexpMainLayoutPackingBounds.prePacking alloc actual.coefficientState (p n)) :=
    mono hm.prePackingBound s2
  have hpack := SubexpMainLayoutPackingBounds.packing_runtimeBound_le
    actual.stages.choices.tailTrace hw2
  have h2 : cs.packingCost ≤ C*(g 2+X+1)^d := by
    apply hpack.trans
    exact cap hc.2.2.1 hd.2.2.1 (by omega) (by omega)
  have s3 : W+cs.prefixCost+cs.coefficientCost+cs.packingCost ≤ g 3 := advance s2 h2
  have hw3 : RelevantWordBound (g 3) actual.packingState := mono hm.packingBound s3
  have hlocal := SubexpMainLayoutMajorants.local_bound alloc hregs actual.packingState
    (goodInput_s_pos (DyadicSchedule.ready_goodInput ready)) (DyadicSchedule.Q_pos n)
    (List.ofFn actual.result.choices.coefficients) (Subexp.CoefficientSearchSemantics.alphabet (p n))
    hw3 actual.stages.choices.tailTrace.localInputs.counter (by simpa using hR) hr hQ hnative
  have h3 : cs.localBasisCost ≤ C*(g 3+X+1)^d :=
    hlocal.trans (cap hc.2.2.2.1 hd.2.2.2.1 le_rfl (by omega))
  have s4 : W+cs.prefixCost+cs.coefficientCost+cs.packingCost+cs.localBasisCost ≤ g 4 := advance s3 h3
  have hw4 : RelevantWordBound (g 4) actual.middle := mono hm.middleBound s4
  have hprime : BinaryArithmetic.toNat (actual.middle.stacks (persistent _ 6)) = p n := by
    rw [actual.result.choices.prefixResult.persistent]
    simpa only [CounterPrograms.value_eq_toNat] using input.prime
  have hprecision : BinaryArithmetic.toNat (actual.middle.stacks (persistent _ 22)) =
      physicalD (alloc := alloc) (a := a)+1 := by
    rw [actual.result.choices.prefixResult.persistent]
    exact input.precision
  have hexp : BinaryArithmetic.toNat (actual.middle.stacks (persistent _ 29)) = (p n)^4-2 := by
    rw [actual.result.choices.prefixResult.persistent]
    exact input.exponent
  obtain ⟨hcache, _, _⟩ := SubexpMainLayoutCacheBounds.polynomial_bounds alloc hw4
    actual.stages.rows.cacheTrace actual.result.rows.cache actual.stages.rows.lagrangeRun
    hprime hprecision hexp
  have h4 : cs.cacheCost ≤ C*(g 4+X+1)^d := by
    apply hcache.trans
    apply (SubexpMainLayoutMajorants.cache_bound (g 4) X (p n) _ hp hD).trans
    exact cap hc.2.2.2.2.1 hd.2.2.2.2.1 le_rfl (by omega)
  have s5 : W+cs.prefixCost+cs.coefficientCost+cs.packingCost+cs.localBasisCost+cs.cacheCost ≤ g 5 :=
    advance s4 h4
  have hw5 : RelevantWordBound (g 5) actual.result.rows.afterLagrange := mono hm.lagrangeBound s5
  have hrows := SubexpMainLayoutRowBounds.afterLagrange_bound
    (List.ofFn actual.result.choices.coefficients) actual.result.choices.packing.packing
    (SubexpMainScheduledLayout.scopes input) actual.degree actual.result.rows actual.stages.rows
    (g 5) hw5 (Subexp.LocalBasisBatchScheduleBounds.scheduled_two_ne_zero n)
  simp only [List.length_ofFn] at hrows
  have hscope := SubexpMainLayoutMajorants.scope_bound input
    (by have := cfg.width_ge_two; omega) hD hδ
  have h5 : cs.rowCost ≤ C*(g 5+X+1)^d := by
    apply hrows.trans
    apply (SubexpMainLayoutMajorants.row_bound (g 5) X (p n) (r n) (DyadicSchedule.Q n)
      (DyadicSchedule.delta cfg.k cfg.T n) _ (DyadicSchedule.R cfg.k cfg.T n) _ cfg.k
      hp hr hQ hδ hD hR hscope).trans
    exact cap hc.2.2.2.2.2 hd.2.2.2.2.2 le_rfl (by omega)
  have s6 : W+cs.prefixCost+cs.coefficientCost+cs.packingCost+cs.localBasisCost+cs.cacheCost+cs.rowCost ≤ g 6 :=
    advance s5 h5
  have ht : actual.steps ≤ g 6+8 := by
    have := run_steps_le actual
    change actual.steps ≤ cs.total at this
    dsimp only [SixCosts.total] at this
    omega
  have hpoly := grow_six_le_polynomial C d X
  have hpos : 1 ≤ (X+1)^(degree d 6) := Nat.one_le_pow _ _ (by omega)
  change actual.steps ≤ (coefficient C d 6+8)*(X+1)^(degree d 6)
  have hg6 : g 6 ≤ coefficient C d 6*(X+1)^(degree d 6) := hpoly
  rw [Nat.add_mul]
  omega

omit [NeZero (r n)] in
include input in
theorem physical_dimension_le : physicalD (alloc := alloc) (a := a) ≤ n := by
  change SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) ≤ n
  rw [input.dimension, input.variableCount]
  apply (ChunkPartition.count_le_iff input.ell_pos).mpr
  calc
    n = n*1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left n input.ell_pos

/-- Every size premise of the finite composition follows from the seed's
actual parameters and the proved native local-search envelope. -/
theorem seed_bound (valid : SubexpMainAssembly.validLeaf cfg n G) (W : ℕ)
    (ha : RelevantWordBound W a) :
    actual.steps ≤ constant cfg.k *
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W (physicalD (alloc := alloc) (a := a))+1)^exponent := by
  let X := SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W (physicalD (alloc := alloc) (a := a))
  have hparts : W ≤ X ∧ p n ≤ X ∧ r n ≤ X ∧ DyadicSchedule.Q n ≤ X ∧
      DyadicSchedule.delta cfg.k cfg.T n ≤ X ∧ DyadicSchedule.R cfg.k cfg.T n ≤ X ∧
      physicalD (alloc := alloc) (a := a) ≤ X ∧
      SubexpMainLayoutScheduleBounds.envelope cfg.k cfg.T n ≤ X := by
    dsimp only [X, SubexpMainLayoutSeedBounds.seed]
    omega
  have hblock : MulticolorTypes.blockSize (r n) ((p n)^4-1)
      (DyadicSchedule.delta cfg.k cfg.T n) ≤
        SubexpMainLayoutScheduleBounds.envelope cfg.k cfg.T n :=
    SubexpMainLayoutScheduleBounds.N_le_envelope cfg.k cfg.T n
  have hprefix : SubexpMainLayoutPrefixBounds.size W n cfg.k cfg.T ≤ X := by
    dsimp only [SubexpMainLayoutPrefixBounds.size, X, SubexpMainLayoutSeedBounds.seed]
    change W+n+cfg.k+p n+(p n)^cfg.k+r n+DyadicSchedule.Q n+
      DyadicSchedule.delta cfg.k cfg.T n+
      MulticolorTypes.blockSize (r n) ((p n)^4-1) (DyadicSchedule.delta cfg.k cfg.T n)+1 ≤ _
    omega
  have hn := DyadicSchedule.ready_goodInput ready
  have hpower := (SubexpMainLayoutScheduleBounds.p_pow_R_le_envelope cfg.k cfg.T n hn).trans
    hparts.2.2.2.2.2.2.2
  have hnative := (SubexpMainLayoutScheduleBounds.sourceBudget_le_envelope cfg.k cfg.T n hn
    (goodInput_s_pos hn) (DyadicSchedule.Q_pos n) (List.ofFn actual.result.choices.coefficients)
    (Subexp.CoefficientSearchSemantics.alphabet (p n)) (by simp)
    (by simp [Subexp.CoefficientSearchSemantics.alphabet])).trans hparts.2.2.2.2.2.2.2
  exact finite_bound actual valid W X ha hparts.1 hprefix hparts.2.1 hparts.2.2.1
    hparts.2.2.2.1 hparts.2.2.2.2.1 hparts.2.2.2.2.2.1 hparts.2.2.2.2.2.2.1
    hpower hnative

end Finite

/-- The complete actual layout call at the real transferred-leaf entry.
The constants and polynomial degree are fixed before the input, boot run,
leaf, pending stream, intermediate states and layout output. The optional
fixed multiplier can include the actual primitive compiler overhead. -/
theorem eventually_bound (cfg : Config) (er : ℕ) (hboot : 32 ≤ workRegs er)
    (alloc : Allocation (mainExtraStacks cfg)) (hregs : 16 ≤ er)
    (factor C0 d0 : ℕ) (hhelper : 672 ≤ helperSize cfg) :
    ∀ᶠ n : ℕ in atTop, ∀ [NeZero (r n)] (F : SAT.CNF (Fin n))
      (boot : SubexpMainBoot.Run cfg hboot F)
      (base : MainState er (mainExtraStacks cfg)) (G : SubexpLeafData.Leaf n) (tail : List Bool),
      SubexpMainInvariant.Invariant cfg boot.setupOutput
        (C0*(Encoding.formulaBitLength F+1)^d0) base →
      SubexpSetupStorage.WordBound (C0*(Encoding.formulaBitLength F+1)^d0) boot.afterSetup →
      SubexpMainAssembly.validLeaf cfg n G →
      ∀ (input : SubexpMainLayoutInput.Ready alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G)
        (ready : DyadicSchedule.Ready cfg.k cfg.T n)
        (actual : SubexpMainScheduledLayout.Run alloc hregs
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) G input ready),
      ((factor*actual.steps : ℕ) : ℝ) ≤
        SubexpComputation.runtimeBound 1 1
          (SubexpMainLayoutSeedBounds.degree cfg.k d0 exponent) (Encoding.formulaBitLength F) n := by
  filter_upwards [SubexpMainLayoutSeedBounds.eventually_seed_pow_le_runtimeBound
    cfg.k cfg.T (factor*constant cfg.k) exponent C0 d0] with n hn
  intro inst F boot base G tail hinvariant hwords valid input ready actual
  let L := Encoding.formulaBitLength F
  let W := C0*(L+1)^d0+(8*cfg.k+5)*(L+1)^(2*cfg.k+1)
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hw : RelevantWordBound W
      (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))) :=
    SubexpMainLayoutInitialBounds.transferred_leaf_bound boot hwords hhelper base hinvariant tail G valid hnL
  have hs := Nat.mul_le_mul_left factor (seed_bound actual valid W hw)
  have hs' : factor*actual.steps ≤ (factor*constant cfg.k)*
      (SubexpMainLayoutSeedBounds.seed cfg.k cfg.T n W
        (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc
          (transferredData (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G)))) )+1)^exponent := by
    simpa only [Nat.mul_assoc] using hs
  exact ((Nat.cast_le (α := ℝ)).mpr hs').trans
    (hn L _ W hnL (physical_dimension_le (input := input)) le_rfl)

end SubexponentialSAT.SubexpMainLayoutBounds

end OAI.Algorithms
