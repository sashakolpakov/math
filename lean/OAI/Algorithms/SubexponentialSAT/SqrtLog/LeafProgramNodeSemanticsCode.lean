import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsGroups
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingSource

namespace OAI.Algorithms

/-! The code-dependent expressions emitted by the actual assignment fold
are connected to the scalar U-expansion, without evaluating U at one. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open IdempotentApplyProgram.Steps (Context)
open AssignmentSemantics
noncomputable section

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

def codeDigits (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) : Fin t → R[X] :=
  fun s => (IdempotentProgram.digitPolynomial
    (RingProgram.scalarRing p t ctx.modulus ctx.cache) code s).map scalar

theorem indicatorPolynomial_eq (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (H : Squarefree.Jet (Fin n) R) :
    AssignmentSemantics.indicatorPolynomial ctx scalar code H =
      indicatorJet t (codeDigits ctx scalar code) H := by
  have hu : Squarefree.Sparse.atom (IdempotentApplyProgram.Multiplier.uKey n) (1:R) =
      (Polynomial.X : Squarefree.Jet (Fin n) R) := by
    simp [Squarefree.Sparse.atom,IdempotentApplyProgram.Multiplier.uKey,
      show Squarefree.monomial (V:=Fin n) ∅ (1:R) = 1 from rfl,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [AssignmentSemantics.indicatorPolynomial,indicatorJet,hu,codeDigits,
    Polynomial.eval₂_map]

theorem codeDigits_degree (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) (s : Fin t) :
    (codeDigits ctx scalar code s).natDegree ≤ 2 := by
  apply Polynomial.natDegree_map_le.trans
  have := IdempotentProgram.digitPolynomial_degree
    (RingProgram.scalarRing p t ctx.modulus ctx.cache) code s
  omega

theorem codeDigits_computed (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (half : RingProgram.ScalarCode p t) :
    codeDigits ctx scalar (IdempotentProgram.coefficientRun
      (RingProgram.scalarRing p t ctx.modulus ctx.cache).program t half).1 =
      fun s => (IdempotentProgram.digitPolynomial
        (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        (IdempotentProgram.coefficientRun
          (RingProgram.scalarRing p t ctx.modulus ctx.cache).program t half).1 s).map scalar := rfl

theorem eval_source_clause {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ v, Moments.jetEval x hx (jet v)=Polynomial.C (path v))
    (clause : List (SAT.Literal (Fin n))) :
    Moments.jetEval x hx (MvPolynomial.eval jet (clausePolynomial (R:=Squarefree.Jet V R) clause)) =
      Polynomial.C (clauseValue (ringAlgebra R[X]) path clause) := by
  rw [← clauseValue_eq_eval (R:=Squarefree.Jet V R) jet clause,map_clauseValue (Moments.jetEval x hx) jet clause]
  simp only [hjet]
  exact (map_clauseValue Polynomial.C path clause).symm

theorem eval_source_row {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ v, Moments.jetEval x hx (jet v)=Polynomial.C (path v))
    (ws : SparseRow (Fin n) R) :
    Moments.jetEval x hx (MvPolynomial.eval jet (rowPolynomial (R:=Squarefree.Jet V R) (scalarJet (V:=V)) ws)) =
      Polynomial.C (rowValue (ringAlgebra R[X]) Polynomial.C path ws) := by
  rw [← rowValue_eq_eval (R:=Squarefree.Jet V R) (scalarJet (V:=V)) jet ws,map_rowValue (Moments.jetEval x hx) (scalarJet (V:=V)) jet ws]
  simp only [hjet,ResidualEmbedding.scalarJet_eq_ringScalar,jetEval_ringScalar]
  exact (map_rowValue Polynomial.C Polynomial.C path ws).symm

/-- Every selected ID maps to its source expansion; unused IDs map to one. -/
theorem selectedValue_eval_at (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hjet : ∀ v, Moments.jetEval x hx (jet id v)=Polynomial.C (path id v)) :
    Moments.jetEval x hx (selectedValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  unfold selectedValue selectedExpression
  simp only [List.length_map]
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi]
    rw [indicatorPolynomial_eq]
    apply indicatorJet_eval _ _ _ x hx
    simpa only [hashPath,Fin.getElem_fin,List.getElem_map] using
      eval_source_row (jet id) (path id) x hx hjet
        (NativeSemantics.sourceTerms (RingProgram.denote
          (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) hashes[id])
  · simp only [dite_eq_right hi]
    by_cases hm : (marked && decide (id=hashes.length))=true
    · simp only [ite_eq_left hm]
      exact eval_source_clause (jet id) (path id) x hx hjet clause
    · simp only [ite_eq_right hm,map_one]

/-- Every selected ID maps to its source expansion; unused IDs map to one. -/
theorem selectedValue_eval (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ id v, Moments.jetEval x hx (jet id v)=Polynomial.C (path id v))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    Moments.jetEval x hx (selectedValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  exact selectedValue_eval_at ctx scalar basis code jet path x hx hashes marked clause id (hjet id)

/-- This applies directly to the canonical product conclusion of
selectedRun_polynomial. It does not assert that U-summation is multiplicative. -/
theorem selected_product_readout (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hjet : ∀ id v, Moments.jetEval x hx (jet id v)=Polynomial.C (path id v))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (ids : List ℕ) :
    Truncation.trunc ctx.J (Moments.sumUCoeff ctx.u (Moments.jetEval x hx
      (Squarefree.canonical ctx.u ctx.J
        ((ids.map (selectedValue ctx scalar basis code jet hashes marked clause)).prod)))) =
    Truncation.trunc ctx.J (Moments.sumUCoeff ctx.u
      ((ids.map (selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path)).prod)) := by
  rw [Moments.evaluated_readout_canonical,map_list_prod]
  simp only [List.map_map,Function.comp_def,selectedValue_eval ctx scalar basis code jet path x hx hjet]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
