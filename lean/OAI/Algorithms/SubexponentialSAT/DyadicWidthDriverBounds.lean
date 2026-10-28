import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthDriverCosts
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleInitializeBounds
import OAI.Algorithms.SubexponentialSAT.DyadicNodeBudget

namespace OAI.Algorithms

/-! Bounds on the actual fixed-width driver, including every initializer,
loader, callback, final counter increment, and scan-control instruction. -/

namespace SubexponentialSAT.DyadicWidthDriverBounds

open CandidatePrepareProgram (formulaCode)
open ExecCNFWidthDriver
open DyadicMaskedSearchBounds DyadicCallbackWordBounds DyadicNodeBudget
open scoped BigOperators

/-- These are properties of the stored input words. In particular, the bank
lengths come from the arithmetic producer, not from the decoded values. -/
structure Inputs (k T n m : ℕ) (F : Formula) (limit : List Bool) (a : Data k) : Prop where
  count : F.length ≤ m
  width : ∀ C ∈ F, C.length ≤ k
  literal : ∀ C ∈ F, ∀ bits ∈ C, bits.length ≤ 2 * n + 1
  limitLength : limit.length ≤ m + 1
  indexWidth : CounterPrograms.value (a.stacks (low k 20)) = DyadicWidth.width m
  indexWidthLength : (a.stacks (low k 20)).length ≤ m + 1
  oldWidth : a.stacks (low k 14) = []
  oldThreshold : a.stacks (low k 15) = []
  bankValue : ∀ d : Width k,
    CounterPrograms.value (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) =
      arity T n (dimension d)
  bankLength : ∀ d : Width k,
    (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (dimension d)) *
          ((SparsificationBudgetProgram.outputWord T (SubexpPackingParameters.s n)).length + 1)

variable {k T n m : ℕ} {F : Formula} {limit : List Bool} {a : Data k}

theorem bank_length_le (h : Inputs k T n m F limit a) (d : Width k) :
    (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length ≤
      thresholdCoefficient k T * localSize n m (threshold k T n) k :=
  threshold_word_length_le k T n m (threshold k T n) d _ (h.bankLength d)

theorem widthCap_le (h : Inputs k T n m F limit a) :
    widthCap k a ≤ k * localSize n m (threshold k T n) k := by
  have hsum : (∑ d : Width k, (dimension d).bits.length) ≤
      ∑ _d : Width k, localSize n m (threshold k T n) k := by
    apply Finset.sum_le_sum
    intro d _
    exact ((SparsificationBudgetProgram.bits_length_le _).trans (dimension_le d)).trans
      (by unfold localSize; omega)
  simpa only [widthCap, h.oldWidth, List.length_nil, Nat.zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      hsum.trans (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (Nat.sub_le k 1))

theorem rowCap_le (h : Inputs k T n m F limit a) :
    rowCap k a ≤ k * (thresholdCoefficient k T * localSize n m (threshold k T n) k) := by
  have hsum : (∑ d : Width k,
      (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length) ≤
      ∑ _d : Width k, thresholdCoefficient k T * localSize n m (threshold k T n) k := by
    exact Finset.sum_le_sum (fun d _ => bank_length_le h d)
  simpa only [rowCap, h.oldThreshold, List.length_nil, Nat.zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      hsum.trans (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (Nat.sub_le k 1))

theorem searchCost_le (h : Inputs k T n m F limit a) (d : Width k) :
    searchCost k d F limit a ≤
      sourceBudget k m (threshold k T n)
        (callbackCoefficient k T * localSize n m (threshold k T n) k ^ 24) +
      (256 * (thresholdCoefficient k T + 1) ^ 3 + 16) *
        localSize n m (threshold k T n) k ^ 3 := by
  let L := localSize n m (threshold k T n) k
  let A := thresholdCoefficient k T
  let r := arity T n (dimension d)
  let rows := a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))
  let bits := a.stacks (low k 20)
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hkL : k ≤ L := by dsimp [L, localSize]; omega
  have hmL : m + 1 ≤ L := by dsimp [L, localSize]; omega
  have hr : r ≤ threshold k T n := arity_le_threshold k T n _ (dimension_le d)
  have hrL : r + 1 ≤ L := by dsimp [L, localSize]; omega
  have hwL : DyadicWidth.width m ≤ L := (DyadicWidth.width_le_succ m).trans hmL
  have hbig : L ≤ (A + 1) * L := by nlinarith
  have hrows : rows.length ≤ A * L := bank_length_le h d
  have hinit : ExecCNFTupleInitialize.bound k rows bits ≤
      256 * (A + 1) ^ 3 * L ^ 3 := by
    have hh := ExecCNFTupleInitialize.bound_le_uniform k rows bits ((A + 1) * L)
      (hL.trans hbig) (hkL.trans hbig)
      (by rw [h.bankValue d]; exact (Nat.le_of_succ_le hrL).trans hbig)
      (by rw [h.indexWidth]; exact hwL.trans hbig)
      (hrows.trans (by nlinarith)) (h.indexWidthLength.trans (hmL.trans hbig))
    simpa only [mul_pow, Nat.mul_assoc] using hh
  have hlocal : localSize n m r k ≤ L := by dsimp [localSize, L]; omega
  have hcallback : callbackBudget F limit (dimension d).bits rows k r (DyadicWidth.width m) ≤
      callbackCoefficient k T * L ^ 24 := by
    exact (callback_envelope_le F n m r k T d limit rows h.count h.width h.literal
      h.limitLength (h.bankLength d)).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlocal 24))
  have hsource := sourceBudget_mono (k := k) (m := m) hr hcallback
  have hproduct : r * DyadicWidth.width m ≤ L ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (Nat.le_of_succ_le hrL) hwL
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL3 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hcleanup : 4 * (k + r * DyadicWidth.width m) + 4 * (r + 1) + 4 ≤ 16 * L ^ 3 := by
    have hbound : 4 * (k + r * DyadicWidth.width m) + 4 * (r + 1) + 4 ≤ 16 * L ^ 2 := by omega
    exact hbound.trans (Nat.mul_le_mul_left 16 hL3)
  have hs := widthSearch_bound_le_masked k m r
    (callbackBudget F limit (dimension d).bits rows k r (DyadicWidth.width m))
    (ExecCNFTupleInitialize.bound k rows bits)
  change ExecCNFWidthSearch.bound k (CounterPrograms.value rows) (CounterPrograms.value bits)
    (callbackBudget F limit (dimension d).bits rows k (CounterPrograms.value rows)
      (CounterPrograms.value bits)) (ExecCNFTupleInitialize.bound k rows bits) ≤ _
  rw [h.bankValue d, h.indexWidth]
  apply hs.trans
  change _ ≤ _ + (256 * (A + 1) ^ 3 + 16) * L ^ 3
  nlinarith only [hinit, hsource, hcleanup]

theorem uniformStageBound_le (h : Inputs k T n m F limit a) (d : Width k) :
    uniformStageBound k d F limit a ≤
      sourceBudget k m (threshold k T n)
        (callbackCoefficient k T * localSize n m (threshold k T n) k ^ 24) +
      stageCoefficient k T * localSize n m (threshold k T n) k ^ 3 := by
  let L := localSize n m (threshold k T n) k
  let A := thresholdCoefficient k T
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hL3 : L ≤ L ^ 3 := by simpa using Nat.pow_le_pow_right hL (show 1 ≤ 3 by decide)
  have hwidth := widthCap_le h
  have hrow := rowCap_le h
  have hbank := bank_length_le h d
  have hbits : (dimension d).bits.length ≤ L :=
    ((SparsificationBudgetProgram.bits_length_le _).trans (dimension_le d)).trans
      (by dsimp [L, localSize]; omega)
  have hload : 2 * widthCap k a + 2 * rowCap k a + 2 * (dimension d).bits.length +
      7 * (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length + 13 ≤
      ((2 * k + 20) * (A + 1)) * L ^ 3 := by
    have hh : 2 * widthCap k a + 2 * rowCap k a + 2 * (dimension d).bits.length +
        7 * (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))).length + 13 ≤
        ((2 * k + 20) * (A + 1)) * L := by
      change widthCap k a ≤ k * L at hwidth
      change rowCap k a ≤ k * (A * L) at hrow
      change _ ≤ A * L at hbank
      nlinarith
    exact hh.trans (Nat.mul_le_mul_left _ hL3)
  have hs := searchCost_le h d
  unfold uniformStageBound
  change _ ≤ _ + stageCoefficient k T * L ^ 3
  dsimp [stageCoefficient]
  change _ ≤ _ + ((2 * k + 20) * (A + 1) + 256 * (A + 1) ^ 3 + 16) * L ^ 3
  nlinarith only [hload, hs]

theorem totalBound_le (h : Inputs k T n m F limit a) :
    totalBound k F limit a ≤
      k * sourceBudget k m (threshold k T n)
        (callbackCoefficient k T * localSize n m (threshold k T n) k ^ 24) +
      (k * stageCoefficient k T + 2 * k + 3) * localSize n m (threshold k T n) k ^ 3 := by
  let L := localSize n m (threshold k T n) k
  let S := sourceBudget k m (threshold k T n) (callbackCoefficient k T * L ^ 24)
  have hsum : ((List.finRange (k - 1)).map (fun d => uniformStageBound k d F limit a)).sum ≤
      (List.finRange (k - 1)).length * (S + stageCoefficient k T * L ^ 3) := by
    induction List.finRange (k - 1) with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hd := uniformStageBound_le h d
      change _ ≤ S + stageCoefficient k T * L ^ 3 at hd
      nlinarith
  have hL : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ (by dsimp [L, localSize]; omega)
  have hk : k - 1 ≤ k := Nat.sub_le k 1
  have hm := Nat.mul_le_mul_right (S + stageCoefficient k T * L ^ 3) hk
  simp only [List.length_finRange] at hsum
  unfold totalBound scanBound
  simp only [List.length_finRange]
  change _ ≤ k * S + (k * stageCoefficient k T + 2 * k + 3) * L ^ 3
  nlinarith

/-- This also reserves the actual formula-size setup, the encoded local
input itself, and the final call/return constants for the node wrapper. -/
theorem totalBound_with_setup_le (h : Inputs k T n m F limit a) :
    totalBound k F limit a + 128 * ((formulaCode F).length + 1) ^ 2 +
        (formulaCode F).length + 3 ≤
      budget k T (overheadCoefficient k T) n m := by
  let L := localSize n m (threshold k T n) k
  let S := sourceBudget k m (threshold k T n) (callbackCoefficient k T * L ^ 24)
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have h36 : L ^ 3 ≤ L ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hL6 : 1 ≤ L ^ 6 := Nat.one_le_pow _ _ hL
  have hf : (formulaCode F).length ≤ 24 * L ^ 3 := by
    have hh := DyadicCallbackInputs.aggregate_canonical_le F n m (threshold k T n) k 0
      h.count h.width h.literal (Nat.zero_le k)
    apply le_trans _ hh
    unfold ExecSunflowerCallbackBounds.aggregate
    omega
  have hf1 : (formulaCode F).length + 1 ≤ 25 * L ^ 3 := by omega
  have hsq : ((formulaCode F).length + 1) ^ 2 ≤ 625 * L ^ 6 := by
    calc
      ((formulaCode F).length + 1) ^ 2 ≤ (25 * L ^ 3) ^ 2 :=
        Nat.pow_le_pow_left hf1 2
      _ = 625 * L ^ 6 := by ring_nf
  have ht := totalBound_le h
  have ht' : totalBound k F limit a ≤
      k * S + (k * stageCoefficient k T + 2 * k + 3) * L ^ 6 :=
    ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h36) _)
  have hf' := hf.trans (Nat.mul_le_mul_left 24 h36)
  change _ ≤ k * S + overheadCoefficient k T * L ^ 6
  unfold overheadCoefficient
  nlinarith only [ht', hsq, hf', hL6]

end SubexponentialSAT.DyadicWidthDriverBounds

end OAI.Algorithms
