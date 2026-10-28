import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixBridge
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl

namespace OAI.Algorithms

/-! Polynomial bounds for the actual source-row interpreter. Intermediate
arrays have exactly D coefficient cells, even when the untruncated source
expression has larger intermediate degree. -/

namespace SubexponentialSAT.SubexpRowCost

open SubexpLiftRing SubexpQuarticRing
open SubexpRowPolynomialCalls (Coefficient encode)
open SubexpRowPostfixBridge (addValue mulValue loadValue addBound mulBound loadBound)

def scale (D B : ℕ) : ℕ := 1000000 * ((D + 1)^3 * (B + 1)^2)

private theorem scalar_bounds (D B : ℕ) :
    31000 * (2 * D + 1) * (B + 1)^2 + 192 * D * B + 83 ≤ scale D B ∧
    601000 * ((D + 1)^3 * (B + 1)^2) + 192 * D * B + 84 ≤ scale D B ∧
    64 * D * B + 63 ≤ scale D B ∧ 23 ≤ scale D B := by
  let A := (D + 1)^3 * (B + 1)^2
  have hD : D + 1 ≤ (D + 1)^3 := by nlinarith [Nat.zero_le (D^2), Nat.zero_le (D^3)]
  have hB : B + 1 ≤ (B + 1)^2 := by nlinarith [Nat.zero_le (B^2)]
  have hA : 1 ≤ A := Nat.succ_le_of_lt (by dsimp [A]; positivity)
  have hDB : D * B ≤ A :=
    (Nat.mul_le_mul (by omega : D ≤ D + 1) (by omega : B ≤ B + 1)).trans
      (Nat.mul_le_mul hD hB)
  have hdim : (2 * D + 1) * (B + 1)^2 ≤ 2 * A := by
    calc
      _ ≤ (2 * (D + 1)^3) * (B + 1)^2 := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * A := by dsimp [A]; ring
  have h192 := Nat.mul_le_mul_left 192 hDB
  have h64 := Nat.mul_le_mul_left 64 hDB
  have h31000 := Nat.mul_le_mul_left 31000 hdim
  dsimp [scale]
  change _ ≤ 1000000 * A ∧ _ ≤ 1000000 * A ∧ _ ≤ 1000000 * A ∧ _ ≤ 1000000 * A
  simp only [Nat.mul_assoc] at h192 h64 h31000 ⊢
  omega

theorem encode_length (p μ : ℕ) (P : List (Coefficient p μ)) :
    (encode P).length = P.length * (4 * baseWidth p μ) :=
  SubexpConvolutionControl.encodeArray_length _ _ (fun a => SubexpFlatAdd.encode_length a) P

theorem addBound_le (p μ D : ℕ) (ops : SubexpSymbolicCost.RingProgram (Coefficient p μ))
    (P Q : List (Coefficient p μ)) (hP : P.length = D) (hQ : Q.length = D) :
    14 + addBound p μ ops P Q ≤ scale D (baseWidth p μ) := by
  have hout : (addValue ops P Q).length = D := by
    rw [addValue, SubexpPolynomialAddService.addProgram_length, hP, hQ, max_self]
  unfold addBound
  rw [encode_length, encode_length, encode_length, hP, hQ, hout]
  calc
    _ = 31000 * (2 * D + 1) * (baseWidth p μ + 1)^2 +
        192 * D * baseWidth p μ + 83 := by ring
    _ ≤ _ := (scalar_bounds D (baseWidth p μ)).1

theorem mulBound_le (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t z : Coefficient p μ) (D : ℕ) (P Q : List (Coefficient p μ))
    (hP : P.length = D) (hQ : Q.length = D) :
    14 + mulBound p μ M t z D P Q ≤ scale D (baseWidth p μ) := by
  have hout : (mulValue p μ M t z D P Q).length = D :=
    SubexpTruncatedMultiply.result_length p μ M t z D P Q
  unfold mulBound
  rw [encode_length, encode_length, encode_length, hP, hQ, hout]
  calc
    _ = 601000 * ((D + 1)^3 * (baseWidth p μ + 1)^2) +
        192 * D * baseWidth p μ + 84 := by ring
    _ ≤ _ := (scalar_bounds D (baseWidth p μ)).2.1

theorem literalBound_le (p μ D : ℕ) (P : List (Coefficient p μ)) :
    11 * (encode P).length + 17 + loadBound p μ D P ≤
      scale D (baseWidth p μ) * ((encode P).length + 1) := by
  have hbase := (scalar_bounds D (baseWidth p μ)).2.2.1
  have h23 := Nat.mul_le_mul_right (encode P).length (scalar_bounds D (baseWidth p μ)).2.2.2
  unfold loadBound
  rw [Nat.mul_add, Nat.mul_one]
  nlinarith only [hbase, h23]

def work {C : Type*} (encode : C → List Bool) : Algorithm.Expr C → ℕ
  | .lit x => (encode x).length + 1
  | .add e f => work encode e + work encode f + 1
  | .mul e f => work encode e + work encode f + 1

theorem work_le_source {C : Type*} (encode : C → List Bool) (e : Algorithm.Expr C) :
    work encode e ≤ (SubexpPostfixControl.serializeCode encode e.compile).length := by
  induction e with
  | lit x => simp [work, Algorithm.Expr.compile, SubexpPostfixControl.serializeCode,
      SubexpPostfixControl.serializeInstr]; omega
  | add e f he hf =>
      simp only [work, Algorithm.Expr.compile, SubexpKernelControl.serializeCode_append,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        List.length_append, List.length_cons, List.length_nil]
      omega
  | mul e f he hf =>
      simp only [work, Algorithm.Expr.compile, SubexpKernelControl.serializeCode_append,
        SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr,
        List.length_append, List.length_cons, List.length_nil]
      omega

theorem expressionCost_le (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t z : Coefficient p μ) (D : ℕ) (ops : SubexpSymbolicCost.RingProgram (Coefficient p μ))
    (e : Algorithm.Expr (List (Coefficient p μ))) :
    letI : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
    letI : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
    SubexpProjectedInterpreter.exprCost encode (addBound p μ ops) (mulBound p μ M t z D)
      (loadValue z D) (loadBound p μ D) e ≤ scale D (baseWidth p μ) * work encode e := by
  let _ : Add (List (Coefficient p μ)) := ⟨addValue ops⟩
  let _ : Mul (List (Coefficient p μ)) := ⟨mulValue p μ M t z D⟩
  have hv := SubexpRowPostfixBridge.validity p μ M t z D ops
  induction e with
  | lit x => exact literalBound_le p μ D x
  | add e f he hf =>
      have hb := addBound_le p μ D ops (e.map (loadValue z D)).eval (f.map (loadValue z D)).eval
        (hv.eval_valid e) (hv.eval_valid f)
      simp only [SubexpProjectedInterpreter.exprCost, work, Nat.mul_add, Nat.mul_one]
      omega
  | mul e f he hf =>
      have hb := mulBound_le p μ M t z D (e.map (loadValue z D)).eval (f.map (loadValue z D)).eval
        (hv.eval_valid e) (hv.eval_valid f)
      simp only [SubexpProjectedInterpreter.exprCost, work, Nat.mul_add, Nat.mul_one]
      omega

end SubexponentialSAT.SubexpRowCost

end OAI.Algorithms
