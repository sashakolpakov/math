import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredLow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramSemantics

namespace OAI.Algorithms

/-! The concrete low-variable output with its executed beta fold, rather than
a supplied beta premise. The full source-row interpretation remains explicit. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

theorem betaValue_pairedRows {B d N : ℕ} {R : Type*} [CommRing R]
    (ops : SubexpSymbolicCost.RepresentedRing (Coeff B d) R) (theta : Coeff B d)
    (rows : List (Fixed.Array B d N × Bool)) :
    betaValue ops theta (pairedRows rows) =
      ∑ v : Fin rows.length,
        (polynomial ops rows[v].1.val).eval (ops.decode theta) *
          (if rows[v].2 then 1 else 0) := by
  have hrows : pairedRows rows = List.ofFn (fun v : Fin rows.length =>
      (rows[v].1.val,rows[v].2)) := by
    simpa only [pairedRows, Fin.getElem_fin] using
      (List.ofFn_getElem_eq_map rows (fun row => (row.1.val,row.2))).symm
  rw [hrows,betaValue,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  cases h : rows[v.val].2 <;> simp [Fin.getElem_fin,h]

noncomputable def nativeStored (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    Moments.Stored (R:=a.O t) (Finset.univ : Finset (Fin rows.length)) u J :=
  outputStored (RingProgram.modelRing t ht hd a M cache) u J hu hJ theta
    (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
    (fun v => rows[v].1.val)

theorem nativeStored_denote (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote =
      canonical u J (Moments.incidenceJet
        (fun v : Fin rows.length => polynomial (RingProgram.modelRing t ht hd a M cache) rows[v].1.val)
        ((RingProgram.modelRing t ht hd a M cache).decode theta)
        (∑ v : Fin rows.length,
          (polynomial (RingProgram.modelRing t ht hd a M cache) rows[v].1.val).eval
            ((RingProgram.modelRing t ht hd a M cache).decode theta) *
              (if rows[v].2 then 1 else 0))) := by
  rw [nativeStored,outputStored_denote,
    PerturbationBetaProgram.runValue_decode t ht hd a M cache,
    betaValue_pairedRows]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
