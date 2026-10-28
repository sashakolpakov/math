import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCode

namespace OAI.Algorithms

/-! Literal-scoped evaluation of the actual selected expression.  Missing
incidences impose no value condition: only literals read by that factor occur
in the hypotheses.  U remains a polynomial variable throughout. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open NodeSemantics
open scoped BigOperators

theorem clauseValue_congr {A V : Type*} (alg : Algebra A) (x y : V → A)
    (ls : List (SAT.Literal V)) (h : ∀ l ∈ ls, x l.variable=y l.variable) :
    clauseValue alg x ls=clauseValue alg y ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hl : literalValue alg x l=literalValue alg y l := by
      simp only [literalValue,h l (by simp)]
    simp only [clauseValue,hl]
    rw [ih (fun a ha => h a (by simp [ha]))]

theorem rowValue_congr {A V C : Type*} (alg : Algebra A) (decode : C → A)
    (x y : V → A) (ws : SparseRow V C)
    (h : ∀ w ∈ ws, ∀ l ∈ w.2, x l.variable=y l.variable) :
    rowValue alg decode x ws=rowValue alg decode y ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rcases w with ⟨c,ls⟩
    simp only [rowValue]
    rw [clauseValue_congr alg x y ls (h (c,ls) (by simp)),
      ih (fun a ha => h a (by simp [ha]))]

variable {R : Type*} [CommRing R] {n : ℕ}

theorem eval_source_clause_scoped {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v)
    (clause : List (SAT.Literal (Fin n)))
    (hjet : ∀ l ∈ clause,
      Moments.jetEval x hx (jet l.variable)=Polynomial.C (path l.variable)) :
    Moments.jetEval x hx
      (MvPolynomial.eval jet (clausePolynomial (R:=Squarefree.Jet V R) clause)) =
      Polynomial.C (clauseValue (ringAlgebra R[X]) path clause) := by
  rw [← clauseValue_eq_eval (R:=Squarefree.Jet V R) jet clause,
    map_clauseValue (Moments.jetEval x hx) jet clause]
  rw [clauseValue_congr _ (fun v => Moments.jetEval x hx (jet v))
    (fun v => Polynomial.C (path v)) clause hjet]
  exact (map_clauseValue Polynomial.C path clause).symm

theorem eval_source_row_scoped {V : Type*} [DecidableEq V]
    (jet : Fin n → Squarefree.Jet V R) (path : Fin n → R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v) (ws : SparseRow (Fin n) R)
    (hjet : ∀ w ∈ ws, ∀ l ∈ w.2,
      Moments.jetEval x hx (jet l.variable)=Polynomial.C (path l.variable)) :
    Moments.jetEval x hx
      (MvPolynomial.eval jet (rowPolynomial (R:=Squarefree.Jet V R)
        (scalarJet (V:=V)) ws)) =
      Polynomial.C (rowValue (ringAlgebra R[X]) Polynomial.C path ws) := by
  rw [← rowValue_eq_eval (R:=Squarefree.Jet V R) (scalarJet (V:=V)) jet ws,
    map_rowValue (Moments.jetEval x hx) (scalarJet (V:=V)) jet ws]
  simp only [ResidualEmbedding.scalarJet_eq_ringScalar,jetEval_ringScalar]
  rw [rowValue_congr _ _ (fun v => Moments.jetEval x hx (jet v))
    (fun v => Polynomial.C (path v)) ws hjet]
  exact (map_rowValue Polynomial.C Polynomial.C path ws).symm

/-- No condition on a variable absent from this factor's raw scope is used. -/
theorem selectedValue_eval_scoped {p t d : ℕ} [Fact p.Prime]
    (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (path : ℕ → Fin n → R[X]) (x : Fin n → R) (hx : ∀ v, x v*x v=x v)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hhash : ∀ (hi : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      Moments.jetEval x hx (jet id l.variable)=Polynomial.C (path id l.variable))
    (hmark : marked=true → id=hashes.length → ∀ l ∈ clause,
      Moments.jetEval x hx (jet id l.variable)=Polynomial.C (path id l.variable)) :
    Moments.jetEval x hx
      (AssignmentSemantics.selectedValue ctx scalar basis code jet hashes marked clause id) =
      selectedExpression t (codeDigits ctx scalar code)
        (hashes.map (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)))
        marked clause path id := by
  unfold AssignmentSemantics.selectedValue selectedExpression
  simp only [List.length_map]
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi]
    rw [indicatorPolynomial_eq]
    apply indicatorJet_eval _ _ _ x hx
    simp only [hashPath,Fin.getElem_fin,List.getElem_map]
    apply eval_source_row_scoped (jet id) (path id) x hx
    intro term ht l hl
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ht
    exact hhash hi w hw l hl
  · simp only [dite_eq_right hi]
    by_cases hm : (marked && decide (id=hashes.length))=true
    · simp only [ite_eq_left hm]
      have hp : marked=true ∧ id=hashes.length := by simpa using hm
      exact eval_source_clause_scoped (jet id) (path id) x hx clause (hmark hp.1 hp.2)
    · simp only [ite_eq_right hm,map_one]

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
