import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsGroups

namespace OAI.Algorithms

/-! The local variable Z is a shift of the common global path T. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*}

def shift (theta : R) : R[X] →+* R[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X+Polynomial.C theta)

@[simp] theorem shift_apply (theta : R) (P : R[X]) :
    shift theta P=P.comp (Polynomial.X+Polynomial.C theta) := rfl

@[simp] theorem shift_C (theta c : R) : shift theta (Polynomial.C c)=Polynomial.C c := by
  simp [shift_apply]

theorem hashPath_shift (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (theta : R) (i : Fin hashes.length) :
    hashPath hashes (fun j v => shift theta (path j v)) i =
      shift theta (hashPath hashes path i) := by
  unfold hashPath
  simpa only [shift_C] using
    (map_rowValue (shift theta) Polynomial.C (path i.val) hashes[i]).symm

theorem markedPath_shift (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X]) (theta : R) :
    markedPath hashes marked clause (fun j v => shift theta (path j v)) =
      shift theta (markedPath hashes marked clause path) := by
  cases hm : marked
  · simp [markedPath]
  · simp only [markedPath,ite_true]
    exact (map_clauseValue (shift theta) (path hashes.length) clause).symm

theorem queryPolynomial_shift (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (theta : R) :
    queryPolynomial t digits hashes marked clause (fun j v => shift theta (path j v)) =
      shift theta (queryPolynomial t digits hashes marked clause path) := by
  unfold queryPolynomial
  rw [map_mul,TotalOrder.map_output,markedPath_shift]
  congr 2
  · funext i j
    unfold digitAt
    split
    · rw [hashPath_shift]
      simp only [shift_apply,Polynomial.comp_assoc]
    · simp
  · funext i
    rw [hashPath_shift]
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat]

/-- Complete selected IDs yield the shifted global query, after the single
retained U coefficient sum. -/
theorem selectedExpressions_readout {n : ℕ} (u J : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X]) (theta : R)
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i∈ids)
    (hm : marked=true → hashes.length∈ids) :
    Truncation.trunc J (Moments.sumUCoeff u ((ids.map (selectedExpression u digits hashes marked clause
      (fun j v => shift theta (path j v)))).prod)) =
      Truncation.trunc J ((queryPolynomial u digits hashes marked clause path).comp
        (Polynomial.X+Polynomial.C theta)) := by
  rw [selectedExpression_product u digits hashes marked clause _ ids hn hh hm,
    queryExpansion_readout,queryPolynomial_shift,shift_apply]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
