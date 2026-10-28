import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeScan

namespace OAI.Algorithms

/-! Exact byte order of the physical row scan. No sparse normalization or
deletion of zero coefficient records is used by this bridge. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram

private theorem entries_coefficientRecords {B d n : ℕ} (v : Fin n)
    (j : ℕ) (cs : List (Coeff B d)) :
    PerturbationEmitProgram.entries v j cs = coefficientRecords v j cs := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp only [PerturbationEmitProgram.entries,coefficientRecords,ih]

theorem coordinateResult_dictionary {B d n : ℕ}
    (ops : RingProgram (Coeff B d)) (J : ℕ) (theta : Coeff B d)
    (v : Fin n) (P : List (Coeff B d))
    (acc : List (Index (Fin n) × Coeff B d)) :
    coordinateResult ops J theta v P (dictionaryBits acc) =
      dictionaryBits ((coefficientRecords v 1
        (shiftedValue ops J theta P).val.tail).reverse ++ acc) := by
  unfold coordinateResult
  rw [←List.map_tail,PerturbationEmitProgram.emitted_typed,entries_coefficientRecords]

def scanRecords {B d : ℕ} (ops : RingProgram (Coeff B d)) (J n N : ℕ)
    (theta : Coeff B d) (j : ℕ) (rows : List (Fixed.Array B d N)) :
    List (Index (Fin n) × Coeff B d) :=
  (rows.zipIdx j).flatMap fun p =>
    if hi : p.2 < n then coefficientRecords ⟨p.2,hi⟩ 1
      (shiftedValue ops J theta p.1.val).val.tail else []

theorem rowsResult_dictionary {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J n N : ℕ) (theta : Coeff B d) (j : ℕ)
    (rows : List (Fixed.Array B d N)) (acc : List (Index (Fin n) × Coeff B d)) :
    rowsResult (scanStep ops J n N theta) j rows (dictionaryBits acc) =
      dictionaryBits ((scanRecords ops J n N theta j rows).reverse ++ acc) := by
  induction rows generalizing j acc with
  | nil => simp [rowsResult,scanRecords]
  | cons p ps ih =>
      simp only [rowsResult]
      by_cases hj : j < n
      · rw [scanStep,dite_eq_left hj,coordinateResult_dictionary,ih]
        simp [scanRecords,List.reverse_append,hj,List.append_assoc]
      · rw [scanStep,dite_eq_right hj,ih]
        simp [scanRecords,hj]

private theorem zipIdx_eq_ofFn {α : Type*} (xs : List α) :
    xs.zipIdx 0 = List.ofFn (fun i : Fin xs.length => (xs[i],i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_zipIdx]

theorem scanRecords_full {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J N : ℕ) (theta : Coeff B d) (rows : List (Fixed.Array B d N)) :
    scanRecords ops J rows.length N theta 0 rows =
      (List.ofFn fun v : Fin rows.length => coefficientRecords v 1
        (shiftedValue ops J theta rows[v].val).val.tail).flatten := by
  unfold scanRecords
  rw [zipIdx_eq_ofFn,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext v
  simp only [Function.comp_apply,dite_eq_left v.isLt]

/-- The high-coordinate branch's single physical record, even when zero, is
exactly the existing constant Stored representation at positive precision. -/
theorem originStored_data {B d n : ℕ} {R : Type*} [CommRing R]
    (ops : SubexpSymbolicCost.RepresentedRing (Coeff B d) R)
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J) (beta : Coeff B d) :
    (constantStored (Finset.univ : Finset (Fin n)) t J (ops.decode beta)).data =
      decodeRecords ops [((Index.origin : Index (Fin n)),beta)] := by
  simp [constantStored,Sparse.constant,ht,hJ,decodeRecords]

/-- Typed endpoint of the actual scan, with a supplied computed beta. -/
theorem fullScan_dictionary {B d : ℕ} (ops : RingProgram (Coeff B d))
    (J N : ℕ) (theta beta : Coeff B d) (rows : List (Fixed.Array B d N)) :
    rowsResult (scanStep ops J rows.length N theta) 0 rows
      (dictionaryBits [((Index.origin : Index (Fin rows.length)),beta)]) =
      dictionaryBits (outputWords ops J theta beta (fun v : Fin rows.length => rows[v].val)) := by
  rw [rowsResult_dictionary,scanRecords_full]
  simp only [outputWords,rawWords,List.reverse_cons]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
