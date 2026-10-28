import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramBasic
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter

namespace OAI.Algorithms

/-! Source-sensitive costs and validity of the generic coefficient-array
interpreter, independently of its native arithmetic implementation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT

def binaryBound (K W : ℕ) : ℕ := K + 20*(W+W) + 8*W + 69

def loadBound (B d J : ℕ) (P : List (Coeff B d)) : ℕ :=
  12*(DensePolynomialProgram.encode P).length + 16*(J*(d*B)) + 46

def executionCost {B d : ℕ} (Ka Km W : ℕ) : Algorithm.Expr (List (Coeff B d)) → ℕ
  | .lit P => 23*(DensePolynomialProgram.encode P).length + 16*W + 63
  | .add e f => executionCost Ka Km W e + executionCost Ka Km W f + 14 + Ka
  | .mul e f => executionCost Ka Km W e + executionCost Ka Km W f + 14 + Km

def literalBytes {B d : ℕ} : Algorithm.Expr (List (Coeff B d)) → ℕ
  | .lit P => (DensePolynomialProgram.encode P).length
  | .add e f => literalBytes e + literalBytes f
  | .mul e f => literalBytes e + literalBytes f

private theorem serializeCode_append {A : Type*} (encode : A → List Bool)
    (xs ys : List (Algorithm.Instr A)) :
    SubexpPostfixControl.serializeCode encode (xs ++ ys) =
      SubexpPostfixControl.serializeCode encode xs ++ SubexpPostfixControl.serializeCode encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [SubexpPostfixControl.serializeCode,ih,List.append_assoc]

/-- Both source instructions and their literal payload are paid by actual
input bits: every instruction has two framing bits. -/
theorem source_length {B d : ℕ} (e : Algorithm.Expr (List (Coeff B d))) :
    (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length =
      2 * (e.size + literalBytes e) := by
  induction e with
  | lit P => simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
      SubexpPostfixControl.serializeInstr,Algorithm.Expr.size,literalBytes]; omega
  | add e f he hf =>
      simp only [Algorithm.Expr.compile,serializeCode_append,List.length_append,he,hf,
        SubexpPostfixControl.serializeCode,SubexpPostfixControl.serializeInstr,
        List.length_cons,List.length_nil,Algorithm.Expr.size,literalBytes]
      omega
  | mul e f he hf =>
      simp only [Algorithm.Expr.compile,serializeCode_append,List.length_append,he,hf,
        SubexpPostfixControl.serializeCode,SubexpPostfixControl.serializeInstr,
        List.length_cons,List.length_nil,Algorithm.Expr.size,literalBytes]
      omega

theorem executionCost_eq {B d : ℕ}
    (ops : SubexpSymbolicCost.RingProgram (Coeff B d)) (J Ka Km : ℕ)
    (e : Algorithm.Expr (List (Coeff B d))) :
    letI : Add (List (Coeff B d)) := ⟨addValue ops⟩
    letI : Mul (List (Coeff B d)) := ⟨mulValue ops J⟩
    SubexpProjectedInterpreter.exprCost DensePolynomialProgram.encode (fun _ _ => Ka)
      (fun _ _ => Km) (loadValue ops J) (loadBound B d J) e =
      executionCost Ka Km (J*(d*B)) e := by
  let _ : Add (List (Coeff B d)) := ⟨addValue ops⟩
  let _ : Mul (List (Coeff B d)) := ⟨mulValue ops J⟩
  induction e with
  | lit P => simp only [SubexpProjectedInterpreter.exprCost,loadBound,executionCost]; omega
  | add e f he hf => simp only [SubexpProjectedInterpreter.exprCost,executionCost,he,hf]; omega
  | mul e f he hf => simp only [SubexpProjectedInterpreter.exprCost,executionCost,he,hf]; omega

theorem executionCost_polynomial {B d : ℕ} (Ka Km W : ℕ)
    (e : Algorithm.Expr (List (Coeff B d))) :
    executionCost Ka Km W e ≤ (e.size + literalBytes e) * (Ka+Km+16*W+100) := by
  induction e with
  | lit P => simp only [executionCost,Algorithm.Expr.size,literalBytes]; nlinarith
  | add e f he hf =>
      simp only [executionCost,Algorithm.Expr.size,literalBytes]
      nlinarith
  | mul e f he hf =>
      simp only [executionCost,Algorithm.Expr.size,literalBytes]
      nlinarith

theorem validity {C : Type*} (ops : SubexpSymbolicCost.RingProgram C) (J : ℕ) :
    letI : Add (List C) := ⟨addValue ops⟩
    letI : Mul (List C) := ⟨mulValue ops J⟩
    SubexpProjectedInterpreter.Validity (fun P : List C => P.length = J) (loadValue ops J) := by
  let _ : Add (List C) := ⟨addValue ops⟩
  let _ : Mul (List C) := ⟨mulValue ops J⟩
  constructor
  · exact SubexpDensePaddingSpec.padCells_length ops.zeroRun.1 J
  · intro P Q hP hQ
    change (SubexpDensePolynomial.addProgram ops P Q).1.length = J
    rw [SubexpPolynomialAddService.addProgram_length,hP,hQ,Nat.max_self]
  · intro P Q _ _
    exact DensePolynomialProgram.result_length ops J P Q

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
