import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComplementColumnBatch
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisComplementBounds

namespace OAI.Algorithms

/-! A uniform quartic bound for the actual complement-column batch program. -/

namespace SubexponentialSAT.SubexpComplementColumnBatch

open BitProgram StructuredCalls Subexp
open GlobalBasisColumns (unary)
open GlobalBasisComplementColumns (LocalData encoded)

theorem encoded_length (qs : List LocalData) :
    (encoded qs).length = 2 * (qs.map (fun q => q.payload.length)).sum + 2 * qs.length + 1 := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [encoded, Encoding.length_encodeList_cons, List.map_cons,
        List.sum_cons, List.length_cons] at ih ⊢
      omega

theorem encoded_reverse_length (qs : List LocalData) :
    (encoded qs.reverse).length = (encoded qs).length := by
  rw [encoded_length, encoded_length, List.map_reverse, List.sum_reverse, List.length_reverse]

theorem blockCost_le_uniform (qs : List LocalData) (count bound : ℕ)
    (h : ∀ i < count, blockStepCost i qs ≤ bound) :
    blockCost qs count ≤ count * (bound + 2) + 2 := by
  induction count with
  | zero => simp [blockCost]
  | succ count ih =>
      have ht := ih (fun i hi => h i (by omega))
      have hh := h count (by omega)
      simp only [blockCost, Nat.add_mul, Nat.one_mul]
      omega

def sizeParameter (count leftoverCount : ℕ) (qs : List LocalData) : ℕ :=
  count + leftoverCount + 2 * (encoded qs).length + 1

def polynomialBound (count leftoverCount : ℕ) (qs : List LocalData) : ℕ :=
  1000 * (sizeParameter count leftoverCount qs)^4

theorem cost_polynomial (count leftoverCount : ℕ) (qs : List LocalData) :
    cost count leftoverCount qs + 1 ≤ polynomialBound count leftoverCount qs := by
  let S := sizeParameter count leftoverCount qs
  have hS : 1 ≤ S := by dsimp [S, sizeParameter]; omega
  have hcount : count ≤ S := by dsimp [S, sizeParameter]; omega
  have hleft : leftoverCount ≤ S := by dsimp [S, sizeParameter]; omega
  have hleft1 : leftoverCount + 1 ≤ S := by dsimp [S, sizeParameter]; omega
  have hbytes : (encoded qs).length ≤ S := by dsimp [S, sizeParameter]; omega
  have hlen : qs.length ≤ S := (GlobalBasisComplementColumns.count_le_encoded qs).trans hbytes
  have hS2 : S ≤ S^2 := by nlinarith
  have hS3 : S ≤ S^3 := hS2.trans (Nat.pow_le_pow_right hS (by decide : 2 ≤ 3))
  have hS4 : S ≤ S^4 := hS2.trans (Nat.pow_le_pow_right hS (by decide : 2 ≤ 4))
  have hS24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have hsteps : ∀ i < count, blockStepCost i qs ≤ 530 * S^3 := by
    intro i hi
    have hc := GlobalBasisComplementColumns.colorCost_polynomial i qs.reverse
    rw [encoded_reverse_length] at hc
    have hbase : i + 2 * (encoded qs).length + 1 ≤ S := by
      dsimp [S, sizeParameter]
      omega
    have hp := Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hbase 3)
    have hc' := hc.trans hp
    unfold blockStepCost
    rw [encoded_reverse_length]
    nlinarith
  have hb := blockCost_le_uniform qs count (530 * S^3) hsteps
  have hbm := Nat.mul_le_mul_right (530 * S^3 + 2) hcount
  have hb' : blockCost qs count ≤ 532 * S^4 + 2 := by nlinarith
  have hprep : prepareCost qs ≤ 24 * S^4 := by
    unfold prepareCost
    nlinarith
  have hl := GlobalBasisColumnBlocks.leftoverCost_bound leftoverCount
  have hl' : GlobalBasisColumnBlocks.leftoverCost leftoverCount + 1 ≤ 60 * S^2 :=
    hl.trans (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left hleft1 2))
  have hfinish : finishCost qs leftoverCount ≤ 77 * S^4 := by
    unfold finishCost
    rw [encoded_reverse_length]
    nlinarith
  change prepareCost qs + blockCost qs count + finishCost qs leftoverCount + 1 ≤ 1000 * S^4
  nlinarith

/-- The quartic envelope bounds an actual primitive run and does not depend
on the length of the old output suffix. -/
theorem primitive_execution_polynomial (count leftoverCount : ℕ) (qs : List LocalData) (d : Data)
    (h0 : d.stacks 0 = unary count) (h22 : d.stacks 22 = encoded qs)
    (h23 : d.stacks 23 = unary qs.length) (h24 : d.stacks 24 = unary leftoverCount)
    (h25 : d.stacks 25 = []) (hr : Ready d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * polynomialBound count leftoverCount qs)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update (Function.update d.stacks 0 []) 3
        (outputPrefix count leftoverCount qs ++ d.stacks 3) := by
  obtain ⟨e, he, hs⟩ := primitive_execution count leftoverCount qs d h0 h22 h23 h24 h25 hr
  exact ⟨e, he.mono (Nat.mul_le_mul_left _ (cost_polynomial count leftoverCount qs)), hs⟩

end SubexponentialSAT.SubexpComplementColumnBatch

end OAI.Algorithms
