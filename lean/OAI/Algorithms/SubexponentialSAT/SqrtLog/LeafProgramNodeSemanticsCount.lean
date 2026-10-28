import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsTarget

namespace OAI.Algorithms

/-! Exact fixed-high query count for the code-derived shared-order target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R K : Type*} [CommRing R] [CommRing K] [DecidableEq K]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Empty clauses have violation one, as in the actual clause interpreter. -/
def violates (clause : List (SAT.Literal V)) (x : V → Bool) : Bool :=
  clause.all (fun l => !(l.eval x))

omit [Fintype V] [DecidableEq V] in
theorem clauseValue_boolean (clause : List (SAT.Literal V)) (x : V → Bool) :
    clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) clause =
      if violates clause x then 1 else 0 := by
  induction clause with
  | nil => simp [clauseValue,ringAlgebra,violates]
  | cons l ls ih =>
    change literalValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) l *
      clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (x v)) ls = _
    rw [ih]
    simp only [violates,List.all_cons]
    cases hl : l.positive <;> cases hx : x l.variable <;>
      simp [literalValue,ringAlgebra,SAT.Literal.eval,HashInput.boolValue,hl,hx]

def sourceHash (hashes : List (SparseRow V R)) (x : V → Bool)
    (i : Fin hashes.length) : R :=
  rowValue (ringAlgebra R) id (fun v => HashInput.boolValue (x v)) hashes[i]

def accepted (rho : R →+* K) (hashes : List (SparseRow V R))
    (marked : Bool) (clause : List (SAT.Literal V)) (x : V → Bool) : Prop :=
  (∀ i, rho (sourceHash hashes x i) = 0) ∧ (marked = true → violates clause x = true)

def fixedHighCount (rho : R →+* K) (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V)) : ℕ :=
  ∑ x : ResidualEmbedding.Free H → Bool,
    if accepted rho hashes marked clause (HighIncidence.glue H high x) then 1 else 0

omit [DecidableEq K] in
theorem fixedHighCount_le (rho : R →+* K) (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V)) :
    fixedHighCount rho H high hashes marked clause ≤ 2^Fintype.card (ResidualEmbedding.Free H) := by
  unfold fixedHighCount
  calc
    _ ≤ ∑ _x : ResidualEmbedding.Free H → Bool, 1 := by
      apply Finset.sum_le_sum
      intro x _
      split <;> omega
    _ = _ := by simp

omit [Fintype V] [DecidableEq V] in
theorem hashPath_origin (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (x : V → Bool) (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
    (i : Fin hashes.length) :
    (hashPath hashes path i).eval 0 = sourceHash hashes x i := by
  unfold hashPath sourceHash
  have h := map_rowValue (Polynomial.evalRingHom (0:R)) Polynomial.C (path i.val) hashes[i]
  change (hashPath hashes path i).eval 0 =
    rowValue (ringAlgebra R) (fun c => c)
      (fun v => HashInput.boolValue (x v)) hashes[i]
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C, hpath] using h

omit [Fintype V] [DecidableEq V] in
theorem markedPath_origin (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X])
    (x : V → Bool) (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v)) :
    (markedPath hashes marked clause path).eval 0 =
      if marked then (if violates clause x then 1 else 0) else 1 := by
  cases hm : marked
  · simp [markedPath]
  · simp only [markedPath,ite_true]
    have h := map_clauseValue (Polynomial.evalRingHom (0:R)) (path hashes.length) clause
    simpa only [Polynomial.coe_evalRingHom,hpath,clauseValue_boolean] using h

omit [Fintype V] [DecidableEq V] in
/-- Local idempotent correctness is required only at the source value. The
  shared truncation is discharged here by nilpotent divisibility. -/
theorem queryPolynomial_origin (rho : R →+* K) (q : R) (t : ℕ) (hq : q^t=0)
    (hker : ∀ y, rho y=0 → q∣y) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (x : V → Bool)
    (hpath : ∀ i v, (path i v).eval 0 = HashInput.boolValue (x v))
    (hres : ∀ i, rho (sourceHash hashes x i)=0 ∨ rho (sourceHash hashes x i)=1 ∨
      rho (sourceHash hashes x i)=2)
    (hdigit : ∀ i, (∑ s : Fin t, (digits s).eval (sourceHash hashes x i) *
      IdempotentProgram.hValue (sourceHash hashes x i)^s.val) =
        if rho (sourceHash hashes x i)=0 then 1 else 0) :
    (queryPolynomial t digits hashes marked clause path).eval 0 =
      if accepted rho hashes marked clause x then 1 else 0 := by
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)),
      q ∣ (Polynomial.evalRingHom (0:R)) (IdempotentProgram.hValue (hashPath hashes path i)) := by
    intro i _
    apply hker
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat,
      Polynomial.coe_evalRingHom,hashPath_origin hashes path x hpath]
    rcases hres i with h|h|h <;> rw [h] <;> ring
  have ho := TotalOrder.map_output_eq_prod (Polynomial.evalRingHom (0:R)) q
    (Finset.univ : Finset (Fin hashes.length)) t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) hh hq
  have he (i : Fin hashes.length) :
      (∑ j ∈ Finset.range t, (Polynomial.evalRingHom (0:R))
        (digitAt digits (hashPath hashes path i) j) *
        (Polynomial.evalRingHom (0:R)) (IdempotentProgram.hValue (hashPath hashes path i))^j) =
      if rho (sourceHash hashes x i)=0 then 1 else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [digitAt,dite_eq_left (Fin.isLt _),Polynomial.coe_evalRingHom,Polynomial.eval_comp,
      hashPath_origin hashes path x hpath,IdempotentProgram.hValue,Polynomial.eval_mul,
      Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_ofNat] using hdigit i
  simp_rw [he] at ho
  simp only [Polynomial.coe_evalRingHom] at ho
  have hp : (∏ i : Fin hashes.length, if rho (sourceHash hashes x i)=0 then (1:R) else 0) =
      if ∀ i, rho (sourceHash hashes x i)=0 then 1 else 0 := by
    split_ifs with h
    · exact Finset.prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i,hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [queryPolynomial,Polynomial.eval_mul,ho,markedPath_origin hashes marked clause path x hpath,hp]
  unfold accepted
  by_cases ha : ∀ i, rho (sourceHash hashes x i)=0 <;>
    cases hm : marked <;> cases hv : violates clause x <;> simp [ha]

/-- The digits here are exactly the finite Newton program's returned array. -/
def computedDigits {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A) (phi : A →+* R)
    (t : ℕ) (half : C) : Fin t → R[X] :=
  fun s => (IdempotentProgram.digitPolynomial ops
    (IdempotentProgram.coefficientRun ops.program t half).1 s).map phi

theorem computedDigits_degree {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A) (phi : A →+* R)
    (t : ℕ) (half : C) (s : Fin t) :
    (computedDigits ops phi t half s).natDegree ≤ 2 := by
  apply Polynomial.natDegree_map_le.trans
  have := IdempotentProgram.digitPolynomial_degree ops
    (IdempotentProgram.coefficientRun ops.program t half).1 s
  omega

theorem target_origin {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A) (phi : A →+* R)
    (rho : R →+* K) (q : R) (t : ℕ) (hq : q^t=0)
    (hker : ∀ y, rho y=0 → q∣y) (half : C) (hhalf : 2*ops.decode half=1)
    (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X])
    (hpath : ∀ x i v, (path x i v).eval 0 = HashInput.boolValue (HighIncidence.glue H high x v))
    (hres : ∀ x i, rho (sourceHash hashes (HighIncidence.glue H high x) i)=0 ∨
      rho (sourceHash hashes (HighIncidence.glue H high x) i)=1 ∨
      rho (sourceHash hashes (HighIncidence.glue H high x) i)=2) :
    (target H t (computedDigits ops phi t half) hashes marked clause path).eval 0 =
      (fixedHighCount rho H high hashes marked clause : R) := by
  simp only [target,Polynomial.eval_finsetSum,fixedHighCount,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply queryPolynomial_origin rho q t hq hker _ hashes marked clause (path x)
    (HighIncidence.glue H high x) (hpath x) (hres x)
  intro i
  simpa only [computedDigits,Polynomial.eval_map] using
    IdempotentProgram.output_polynomial_indicator ops phi rho t half hhalf q hq hker
      (sourceHash hashes (HighIncidence.glue H high x) i) (hres x i)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
