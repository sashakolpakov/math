import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDensePaddingSpec
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionAlgebra

namespace OAI.Algorithms

/-!
# Complete source rows from the concrete padded arithmetic

The operations below are definitionally the value operations of
`SubexpRowPostfixBridge`: literal padding, the represented dense addition
program, and the fixed truncated-convolution schedule using the prepared
binary quartic operations. Keeping this semantic file independent of the
physical controller avoids an import cycle at its final correctness theorem.

The only row-specific hypothesis in `eval_full_row` is the degree bound on
the final source polynomial. No intermediate degree bound is required, and
no source-field arithmetic is commuted through the coefficient section.
The physical evaluator and coefficientwise lifting are separate programs.
-/

namespace SubexponentialSAT.SubexpRowSourceSemantics

open SubexpSymbolicCost SubexpSelectedConversions

private theorem evalWith_eq_eval_map {B C : Type*} (literal : B → C)
    (add mul : C → C → C) (e : Algorithm.Expr B) :
    letI : Add C := ⟨add⟩
    letI : Mul C := ⟨mul⟩
    SubexpDensePaddingSpec.evalWith literal add mul e = (e.map literal).eval := by
  let _ : Add C := ⟨add⟩
  let _ : Mul C := ⟨mul⟩
  induction e with
  | lit b => rfl
  | add e f he hf =>
      change add (SubexpDensePaddingSpec.evalWith literal add mul e)
        (SubexpDensePaddingSpec.evalWith literal add mul f) =
          add (e.map literal).eval (f.map literal).eval
      rw [he, hf]
  | mul e f he hf =>
      change mul (SubexpDensePaddingSpec.evalWith literal add mul e)
        (SubexpDensePaddingSpec.evalWith literal add mul f) =
          mul (e.map literal).eval (f.map literal).eval
      rw [he, hf]

variable {p : ℕ} [Fact p.Prime] (source : Prepared p 0)

abbrev Coefficient (p : ℕ) := QuarticCode p 0

/-- These are the unchanged executable source-ring addition callbacks. -/
def addValue (P Q : List (Coefficient p)) : List (Coefficient p) :=
  (SubexpDensePolynomial.addProgram source.program P Q).1

/-- Exactly the update schedule used by the physical truncated multiplier. -/
def mulValue (N : ℕ) (P Q : List (Coefficient p)) : List (Coefficient p) :=
  TruncatedConvolution.run source.zero
    (fun a b => (SubexpPreparedQuartic.binaryAdd p 1 source.modulus a b).1)
    (fun a b =>
      (SubexpPreparedQuartic.binaryMul p 1 source.modulus source.reduction a b).1)
    N P Q

def loadValue (N : ℕ) (P : List (Coefficient p)) : List (Coefficient p) :=
  SubexpDensePaddingSpec.padCells source.zero N P

/-- This decoder is used only in the specification, never in execution. -/
noncomputable def denote (P : List (Coefficient p)) : Polynomial (SubexpActualRing.E p) :=
  PolynomialAlgorithm.denote (P.map source.residueRing.decode)

/-- The value evaluated by the concrete postfix controller. -/
def run (N : ℕ) (e : Algorithm.Expr (List (Coefficient p))) : List (Coefficient p) :=
  SubexpDensePaddingSpec.evalWith (loadValue source N)
    (addValue source) (mulValue source N) e

@[simp] theorem loadValue_length (N : ℕ) (P : List (Coefficient p)) :
    (loadValue source N P).length = N :=
  SubexpDensePaddingSpec.padCells_length source.zero N P

@[simp] theorem addValue_length (P Q : List (Coefficient p)) :
    (addValue source P Q).length = max P.length Q.length := by
  change (SubexpDensePolynomial.addProgram source.residueRing.program P Q).1.length = _
  rw [SubexpDensePolynomial.addProgram_run, SubexpDensePolynomial.addRun_length]

@[simp] theorem mulValue_length (N : ℕ) (P Q : List (Coefficient p)) :
    (mulValue source N P Q).length = N :=
  TruncatedConvolution.run_length _ _ _ _ _ _

theorem denote_loadValue (N : ℕ) (P : List (Coefficient p)) :
    denote source (loadValue source N P) = Truncation.trunc N (denote source P) := by
  exact SubexpDensePaddingSpec.denote_padCells source.residueRing.decode source.zero
    source.residueRing.zero_correct N P

theorem denote_addValue (P Q : List (Coefficient p)) :
    denote source (addValue source P Q) = denote source P + denote source Q := by
  change PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList source.residueRing
    (SubexpDensePolynomial.addProgram source.residueRing.program P Q).1) =
      PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList source.residueRing P) +
      PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList source.residueRing Q)
  rw [SubexpDensePolynomial.addProgram_run, SubexpDensePolynomial.addRun_correct,
    PolynomialAlgorithm.denote_add]

theorem denote_mulValue (N : ℕ) (P Q : List (Coefficient p)) :
    denote source (mulValue source N P Q) =
      Truncation.trunc N (denote source P * denote source Q) := by
  exact SubexpConvolutionAlgebra.run_correct source.residueRing.decode
    (fun a b => (SubexpPreparedQuartic.binaryAdd p 1 source.modulus a b).1)
    (fun a b =>
      (SubexpPreparedQuartic.binaryMul p 1 source.modulus source.reduction a b).1)
    source.residueRing.add_correct source.residueRing.mul_correct
    source.zero source.residueRing.zero_correct N P Q

/-- Every actual operation preserves the fixed cell count, and the resulting
polynomial is the truncation of the complete source expression. -/
theorem run_spec (N : ℕ) (e : Algorithm.Expr (List (Coefficient p))) :
    (run source N e).length = N ∧
      denote source (run source N e) =
        Truncation.trunc N ((e.map (denote source)).eval) := by
  apply SubexpDensePaddingSpec.evalWith_correct N (fun P => P.length = N)
    (loadValue source N) (addValue source) (mulValue source N)
    (denote source) (denote source)
  · intro P
    exact ⟨loadValue_length source N P, denote_loadValue source N P⟩
  · intro P Q hP hQ
    exact ⟨by rw [addValue_length, hP, hQ, max_self], denote_addValue source P Q⟩
  · intro P Q _ _
    exact ⟨mulValue_length source N P Q, denote_mulValue source N P Q⟩

theorem run_full_row (N : ℕ) (e : Algorithm.Expr (List (Coefficient p)))
    (hdegree : ((e.map (denote source)).eval).natDegree < N) :
    denote source (run source N e) = (e.map (denote source)).eval := by
  rw [(run_spec source N e).2]
  ext i
  rw [Truncation.coeff_trunc]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdegree.trans_le (by omega))).symm

/-- Match the custom `Add` and `Mul` instances used in the machine endpoint. -/
theorem run_eq_eval (N : ℕ) (e : Algorithm.Expr (List (Coefficient p))) :
    letI : Add (List (Coefficient p)) := ⟨addValue source⟩
    letI : Mul (List (Coefficient p)) := ⟨mulValue source N⟩
    run source N e = (e.map (loadValue source N)).eval :=
  evalWith_eq_eval_map _ _ _ _

/-- The concrete postfix value has exactly the requested number of cells,
as well as the truncated source denotation. -/
theorem eval_spec (N : ℕ) (e : Algorithm.Expr (List (Coefficient p))) :
    letI : Add (List (Coefficient p)) := ⟨addValue source⟩
    letI : Mul (List (Coefficient p)) := ⟨mulValue source N⟩
    ((e.map (loadValue source N)).eval).length = N ∧
      denote source ((e.map (loadValue source N)).eval) =
        Truncation.trunc N ((e.map (denote source)).eval) := by
  let _ : Add (List (Coefficient p)) := ⟨addValue source⟩
  let _ : Mul (List (Coefficient p)) := ⟨mulValue source N⟩
  rw [← run_eq_eval source N e]
  exact run_spec source N e

/-- The physical evaluator's exact output denotes the full source polynomial.
Its degree premise applies only to the final row; intermediate multiplication
may exceed the retained dimension. -/
theorem eval_full_row (N : ℕ) (e : Algorithm.Expr (List (Coefficient p)))
    (hdegree : ((e.map (denote source)).eval).natDegree < N) :
    letI : Add (List (Coefficient p)) := ⟨addValue source⟩
    letI : Mul (List (Coefficient p)) := ⟨mulValue source N⟩
    denote source ((e.map (loadValue source N)).eval) =
      (e.map (denote source)).eval := by
  let _ : Add (List (Coefficient p)) := ⟨addValue source⟩
  let _ : Mul (List (Coefficient p)) := ⟨mulValue source N⟩
  rw [← run_eq_eval source N e]
  exact run_full_row source N e hdegree

/-- The layout bound `degree ≤ R` supplies the actual retained dimension
`R+1` used by the source-row interpreter. -/
theorem eval_full_row_succ (R : ℕ) (e : Algorithm.Expr (List (Coefficient p)))
    (hdegree : ((e.map (denote source)).eval).natDegree ≤ R) :
    letI : Add (List (Coefficient p)) := ⟨addValue source⟩
    letI : Mul (List (Coefficient p)) := ⟨mulValue source (R + 1)⟩
    denote source ((e.map (loadValue source (R + 1))).eval) =
      (e.map (denote source)).eval :=
  eval_full_row source (R + 1) e (Nat.lt_succ_of_le hdegree)

end SubexponentialSAT.SubexpRowSourceSemantics

end OAI.Algorithms
