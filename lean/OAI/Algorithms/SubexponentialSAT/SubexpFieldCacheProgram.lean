import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCachePairLoop
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCachePreparation

namespace OAI.Algorithms

/-! Complete physical production of the four packed source-field arrays. -/

namespace SubexponentialSAT.SubexpFieldCacheProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl SubexpFieldCacheControl
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheMachine (negate add power)
open SubexpFieldCacheNodeLoop (PowerValue negativeBytes)
open SubexpFieldCachePairLoop (PairValue)

def negativeWords (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (minusOne : Word (baseWidth p μ)) (xs : List (Quad (Word (baseWidth p μ)))) :=
  xs.map (SubexpQuarticNegMachine.negateWords p μ M minusOne)

theorem negativeWords_flat (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (minusOne : Word (baseWidth p μ)) (xs : List (Quad (Word (baseWidth p μ)))) :
    (negativeWords p μ M minusOne xs).flatMap flat = negativeBytes p μ M minusOne xs := by
  simp [negativeWords, negativeBytes, List.flatMap_map]

def resultFrame (frame : Fin 110 → List Bool) (nodes negatives differences : List Bool) :=
  Function.update (Function.update (Function.update frame 97 nodes) 100 negatives) 103 differences

theorem output_lengths (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → ZMod (p^μ)) (exponent : List Bool)
    (xs ys : List (Quad (Word (baseWidth p μ))))
    (rows : List (List (Quad (Word (baseWidth p μ)))))
    (hys : List.Forall₂ (PowerValue p μ c exponent) xs ys)
    (hrows : List.Forall₂ (fun node row => List.Forall₂ (PairValue p μ c exponent node)
      (negativeWords p μ M minusOne xs) row) xs rows) :
    (ys.flatMap flat).length = 4 * baseWidth p μ * xs.length ∧
      (negativeBytes p μ M minusOne xs).length = 4 * baseWidth p μ * xs.length ∧
      (rows.flatten.flatMap flat).length = 4 * baseWidth p μ * xs.length * xs.length := by
  constructor
  · rw [SubexpFieldCacheNodeLoop.flatMap_length, ← hys.length_eq]
  constructor
  · exact SubexpFieldCacheNodeLoop.negativeBytes_length p μ M minusOne xs
  · rw [SubexpFieldCacheNodeLoop.flatMap_length, SubexpFieldCachePairLoop.rows_length hrows]
    simp [negativeWords, Nat.mul_assoc]

def budget (B : ℕ) (exponent : List Bool) (count : ℕ) : ℕ :=
  (18 * (4 * B * count) + 15 * count + 7) + (28 * B + 5) +
    SubexpFieldCacheNodeLoop.passBudget B exponent count +
    SubexpFieldCachePairLoop.passBudget B exponent count count + (8 * B + 3)

/-- A complete execution starting from physically framed node records.
Every output word comes from a concrete arithmetic execution. -/
theorem command_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ) (hblock : base.blockWidth = [])
    (hB : 0 < baseWidth p μ) (xs : List (Quad (Word (baseWidth p μ))))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (hsource : frame 97 = ProgramEncoding.encodeRecords (xs.map flat))
    (hnegative : frame 100 = []) (hdifference : frame 103 = []) (houter : frame 106 = []) :
    ∃ n rf ys rows, n ≤ budget (baseWidth p μ) base.exponent xs.length ∧
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      List.Forall₂ (fun node row => List.Forall₂ (PairValue p μ c base.exponent node)
        (negativeWords p μ M minusOne xs) row) xs rows ∧
      Eval (SubexpFieldCacheMachine.command) n
        (state regs frame (SubexpFieldCacheNodeLoop.ready base [] []))
        (state rf (resultFrame frame (xs.flatMap flat)
          (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat))
          (SubexpFieldCacheNodeLoop.ready base [] (ys.flatMap flat))) := by
  let w0 := SubexpFieldCacheNodeLoop.ready base [] []
  let f1 := Function.update frame 97 (xs.flatMap flat)
  obtain ⟨nf, rf, hnf, hf⟩ := SubexpFieldCachePreparation.flatten_eval
    regs frame w0 (xs.map flat) hsource rfl rfl
  have hf' : Eval SubexpFieldCacheControl.flatten nf (state regs frame w0)
      (state rf f1 w0) := by
    simpa only [← List.flatMap_def, f1] using hf
  let prepared : Words := {base with blockWidth := base.unit}
  let r1 := readRegs rf 0 1 none
  have hwid := SubexpFieldCachePreparation.copy_width_eval rf f1 w0 hblock
  have hwid' : Eval (SubexpFieldCacheControl.copy 93 104) (28 * baseWidth p μ + 5)
      (state rf f1 w0)
      (state r1 f1 (SubexpFieldCacheNodeLoop.ready prepared [] [])) := by
    simpa only [w0, SubexpFieldCacheNodeLoop.ready, prepared, r1, hone,
      SubexpQuarticFlatMul.flat_length,
      show 7 * (4 * baseWidth p μ) = 28 * baseWidth p μ by omega] using hwid
  have hpblock : prepared.blockWidth.length = 4 * baseWidth p μ := by
    simp only [prepared, hone, SubexpQuarticFlatMul.flat_length]
  obtain ⟨nn, rn, ys, hnn, hyn, hn⟩ := SubexpFieldCacheNodeLoop.pass_value
    p μ M c t unit minusOne ht hu prepared hm hr hone hmone hw hpblock hB
    xs r1 f1 (by simp [f1]) (by simpa [f1] using hnegative)
  let f2 := Function.update f1 100 (negativeBytes p μ M minusOne xs)
  let pairbase : Words := {prepared with accumulator := ys.flatMap flat}
  obtain ⟨np, rp, rows, hnp, hyr, hp⟩ := SubexpFieldCachePairLoop.pass_value
    p μ M c t unit ht hu pairbase hm hr hone hw hpblock hB
    xs (negativeWords p μ M minusOne xs) rn f2
    (by simp [f2, f1]) (by simp only [f2, Function.update_same, negativeWords_flat])
    (by simpa [f2, f1] using houter) (by simpa [f2, f1] using hdifference)
  let f3 := Function.update f2 103 (rows.flatten.flatMap flat)
  have hclear := SubexpFieldCachePreparation.clear_width_eval rp f3
    (SubexpFieldCachePairLoop.ready pairbase [] [])
  have hclear' : Eval (clear 104) (8 * baseWidth p μ + 3)
      (state rp f3 (SubexpFieldCachePairLoop.ready pairbase [] []))
      (state (readRegs rp 0 1 none) f3
        (SubexpFieldCacheNodeLoop.ready base [] (ys.flatMap flat))) := by
    simpa only [SubexpFieldCachePairLoop.ready, SubexpFieldCacheNodeLoop.ready,
      pairbase, prepared, hone, SubexpQuarticFlatMul.flat_length, hblock,
      show 2 * (4 * baseWidth p μ) = 8 * baseWidth p μ by omega] using hclear
  have he := hf'.seq (hwid'.seq (hn.seq (hp.seq hclear')))
  refine ⟨_, readRegs rp 0 1 none, ys, rows, ?_, hyn, hyr, he⟩
  have hsum : ((xs.map flat).map List.length).sum = 4 * baseWidth p μ * xs.length := by
    rw [← List.length_flatten, ← List.flatMap_def, SubexpFieldCacheNodeLoop.flatMap_length]
  simp only [SubexpRecordFlatten.bound, hsum, List.length_map] at hnf
  simp only [negativeWords, List.length_map, pairbase, prepared] at hnp
  change nn ≤ SubexpFieldCacheNodeLoop.passBudget (baseWidth p μ) base.exponent xs.length at hnn
  unfold budget
  omega

theorem program_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ) (hblock : base.blockWidth = [])
    (hB : 0 < baseWidth p μ) (xs : List (Quad (Word (baseWidth p μ))))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (hsource : frame 97 = ProgramEncoding.encodeRecords (xs.map flat))
    (hnegative : frame 100 = []) (hdifference : frame 103 = []) (houter : frame 106 = []) :
    ∃ rf ys rows,
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      List.Forall₂ (fun node row => List.Forall₂ (PairValue p μ c base.exponent node)
        (negativeWords p μ M minusOne xs) row) xs rows ∧
      RunsIn SubexpFieldCacheMachine.program (budget (baseWidth p μ) base.exponent xs.length + 1)
        ((state regs frame (SubexpFieldCacheNodeLoop.ready base [] [])).withPC
          (some SubexpFieldCacheMachine.program.entry))
        ((state rf (resultFrame frame (xs.flatMap flat)
          (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat))
          (SubexpFieldCacheNodeLoop.ready base [] (ys.flatMap flat))).withPC none) := by
  obtain ⟨n, rf, ys, rows, hn, hys, hrows, he⟩ := command_value
    p μ M c t unit minusOne ht hu base hm hr hone hmone hw hblock hB xs regs frame
    hsource hnegative hdifference houter
  exact ⟨rf, ys, rows, hys, hrows, n + 1, Nat.add_le_add_right hn 1,
    compiled_halt_trace he 97 103⟩

def stepBound (W : ℕ) : ℕ :=
  500000 * (W + 1)^3 + 25000 * (W + 1)^2 + 128 * W + 28

def nodeBound (W : ℕ) : ℕ := W * (stepBound W + 100 * W + 2) + 21

def rowBound (W : ℕ) : ℕ := W * (stepBound W + 2) + 64 * W + 28 * W^2 + 21

def pairBound (W : ℕ) : ℕ := W * (rowBound W + 2) + 28 * W^2 + 36 * W^3 + 15

/-- An explicit degree-five bound in a common bound for the node count,
coefficient width, exponent bit length, and exponent value. -/
def polynomialBound (W : ℕ) : ℕ :=
  72 * W^2 + 15 * W + 7 + (28 * W + 5) + nodeBound W + pairBound W + (8 * W + 3)

theorem budget_le (B : ℕ) (exponent : List Bool) (count W : ℕ)
    (hB : B ≤ W) (hE : exponent.length ≤ W)
    (hN : BinaryArithmetic.toNat exponent ≤ W) (hcount : count ≤ W) :
    budget B exponent count ≤ polynomialBound W := by
  have hp := SubexpQuarticPowerProgram.runtimeBound_le B exponent W hB hE hN
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hB 1) 2
  have h25 := Nat.mul_le_mul_left 25000 hs
  have h128 := Nat.mul_le_mul_left 128 hB
  have hnodeStep : SubexpFieldCacheMachine.nodeIterationBudget B exponent ≤ stepBound W := by
    unfold SubexpFieldCacheMachine.nodeIterationBudget stepBound
    omega
  have hpairStep : SubexpFieldCacheMachine.pairIterationBudget B exponent ≤ stepBound W := by
    unfold SubexpFieldCacheMachine.pairIterationBudget stepBound
    omega
  have h100 := Nat.mul_le_mul_left 100 hB
  have hnodeProd := Nat.mul_le_mul hcount
    (show SubexpFieldCacheMachine.nodeIterationBudget B exponent + 100 * B + 2 ≤
      stepBound W + 100 * W + 2 by omega)
  have hn : SubexpFieldCacheNodeLoop.passBudget B exponent count ≤ nodeBound W := by
    unfold SubexpFieldCacheNodeLoop.passBudget nodeBound
    omega
  have hBC := Nat.mul_le_mul hB hcount
  have h28 := Nat.mul_le_mul_left 28 hBC
  have h64 := Nat.mul_le_mul_left 64 hB
  have hrowProd := Nat.mul_le_mul hcount (Nat.add_le_add_right hpairStep 2)
  have hrow : SubexpFieldCachePairLoop.rowBudget B exponent count (4 * B * count) ≤
      rowBound W := by
    unfold SubexpFieldCachePairLoop.rowBudget rowBound
    nlinarith only [hrowProd, h64, h28]
  have hpairProd := Nat.mul_le_mul hcount (Nat.add_le_add_right hrow 2)
  have hBQQ := Nat.mul_le_mul hBC hcount
  have h36 := Nat.mul_le_mul_left 36 hBQQ
  have hpair : SubexpFieldCachePairLoop.passBudget B exponent count count ≤ pairBound W := by
    unfold SubexpFieldCachePairLoop.passBudget pairBound
    nlinarith only [hpairProd, h28, h36]
  have h72 := Nat.mul_le_mul_left 72 hBC
  have h15 := Nat.mul_le_mul_left 15 hcount
  have hparse : 18 * (4 * B * count) + 15 * count + 7 ≤ 72 * W^2 + 15 * W + 7 := by
    nlinarith only [h72, h15]
  have hwidth := Nat.mul_le_mul_left 28 hB
  have hclear := Nat.mul_le_mul_left 8 hB
  unfold budget polynomialBound
  omega

end SubexponentialSAT.SubexpFieldCacheProgram

end OAI.Algorithms
