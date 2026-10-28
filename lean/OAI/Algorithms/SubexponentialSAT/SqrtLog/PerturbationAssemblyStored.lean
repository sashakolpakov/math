import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyModel

namespace OAI.Algorithms

/-! The actual fixed-array Horner output is already valid Stored data.
The native order is reversed and zero coefficients are deliberately kept. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

variable {B d n : ℕ} {R : Type*} [CommRing R]

def outputWords (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    List (Index (Fin n) × Coeff B d) :=
  rawWords beta (fun v => (shiftedValue ops J theta (rows v)).val.tail)

theorem outputWords_nodup (ops : RingProgram (Coeff B d)) (J : ℕ)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    ((outputWords ops J theta beta rows).map Prod.fst).Nodup :=
  rawWords_nodup _ _

private theorem shifted_tail_length (ops : RingProgram (Coeff B d))
    (J : ℕ) (hJ : 0 < J) (theta : Coeff B d) (p : List (Coeff B d)) :
    (shiftedValue ops J theta p).val.tail.length < J := by
  rw [List.length_tail,(shiftedValue ops J theta p).property]
  omega

theorem outputWords_valid (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Sparse.ValidData Finset.univ t J
      (decodeRecords ops (outputWords ops.program J theta beta rows)) :=
  rawWords_valid ops t J ht hJ beta _
    (fun v => shifted_tail_length ops.program J hJ theta (rows v))

def outputStored (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Moments.Stored (R:=R) (Finset.univ : Finset (Fin n)) t J where
  data := decodeRecords ops (outputWords ops.program J theta beta rows)
  valid := outputWords_valid ops t J ht hJ theta beta rows
  nodup := by
    simpa [Sparse.keys,decodeRecords,List.map_map,Function.comp_def] using
      outputWords_nodup ops.program J theta beta rows

theorem shifted_tail_polynomial (ops : RepresentedRing (Coeff B d) R)
    (J : ℕ) (theta : Coeff B d) (p : List (Coeff B d)) :
    Polynomial.X * polynomial ops (shiftedValue ops.program J theta p).val.tail =
      Truncation.trunc J (Moments.rowDelta (polynomial ops p) (ops.decode theta)) := by
  apply tail_polynomial_eq_trunc_delta
  exact shiftedValue_denote ops J theta p

theorem outputWords_denote (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    Sparse.denote (decodeRecords ops (outputWords ops.program J theta beta rows)) =
      canonical t J (Moments.incidenceJet (fun v => polynomial ops (rows v))
        (ops.decode theta) (ops.decode beta)) := by
  apply rawWords_canonical_denote ops t J ht hJ beta
  intro v
  exact shifted_tail_polynomial ops J theta (rows v)

theorem outputStored_denote (ops : RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (theta beta : Coeff B d) (rows : Fin n → List (Coeff B d)) :
    (outputStored ops t J ht hJ theta beta rows).denote =
      canonical t J (Moments.incidenceJet (fun v => polynomial ops (rows v))
        (ops.decode theta) (ops.decode beta)) :=
  outputWords_denote ops t J ht hJ theta beta rows

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
