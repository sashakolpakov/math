import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeLiteral

namespace OAI.Algorithms

/-! Exact, valid sparse payloads for both branches of the actual literal
producer. Original ambient IDs are retained and no zero records are removed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram PerturbationProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open Squarefree.Sparse
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def payloadWords (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ) :
    List (Index (Fin rows.length) × Coeff (baseWidth 3 t) d) :=
  if (s 574).getD j false then
    [(Index.origin,if (s 575).getD j false then (RingProgram.modelProgram t a M cache).oneRun.1
      else (RingProgram.modelProgram t a M cache).zeroRun.1)]
  else outputWords (RingProgram.modelProgram t a M cache) J theta
    (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)

theorem nativeLiteralValue_dictionary (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ)
    (hzero : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1) :
    nativeLiteralValue t a M cache J N theta rows s j =
      dictionaryBits (payloadWords t a M cache J N theta rows s j) := by
  cases hh : (s 574).getD j false
  · simpa only [nativeLiteralValue,payloadWords,hh,Bool.false_eq_true,ite_false] using
      lowOutput_dictionary t a M cache J N theta rows
  · cases hb : (s 575).getD j false
    · simpa only [nativeLiteralValue,payloadWords,hh,ite_true,hb,Bool.false_eq_true,
        ite_false,hzero] using origin_dictionary rows.length
          (RingProgram.modelProgram t a M cache).zeroRun.1
    · simpa only [nativeLiteralValue,payloadWords,hh,ite_true,hb,hone] using
        origin_dictionary rows.length (RingProgram.modelProgram t a M cache).oneRun.1

theorem payloadWords_nodup (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ) :
    ((payloadWords t a M cache J N theta rows s j).map Prod.fst).Nodup := by
  unfold payloadWords
  split
  · simp
  · exact outputWords_nodup _ _ _ _ _

theorem payloadWords_valid (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ) :
    Sparse.ValidData Finset.univ u J
      (decodeRecords (RingProgram.modelRing t ht hd a M cache)
        (payloadWords t a M cache J N theta rows s j)) := by
  unfold payloadWords
  split
  · rw [←originStored_data (RingProgram.modelRing t ht hd a M cache) u J hu hJ]
    exact (constantStored _ _ _ _).valid
  · exact outputWords_valid (RingProgram.modelRing t ht hd a M cache) u J hu hJ _ _ _

noncomputable def payloadStored (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ) :
    Moments.Stored (R:=a.O t) (Finset.univ : Finset (Fin rows.length)) u J where
  data := decodeRecords (RingProgram.modelRing t ht hd a M cache)
    (payloadWords t a M cache J N theta rows s j)
  valid := payloadWords_valid t ht hd a M cache u J N hu hJ theta rows s j
  nodup := by
    simpa [Sparse.keys,decodeRecords,List.map_map,Function.comp_def] using
      payloadWords_nodup t a M cache J N theta rows s j

theorem payloadStored_low_denote (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ)
    (hh : (s 574).getD j false = false) :
    (payloadStored t ht hd a M cache u J N hu hJ theta rows s j).denote =
      (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote := by
  simp only [Moments.Stored.denote,payloadStored,payloadWords,hh,Bool.false_eq_true,
    ite_false,nativeStored,outputStored] ; rfl

theorem payloadStored_high_denote (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ)
    (hh : (s 574).getD j false = true) :
    (payloadStored t ht hd a M cache u J N hu hJ theta rows s j).denote =
      canonical u J (atom Index.origin
        (if (s 575).getD j false then (1 : a.O t) else 0)) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change Sparse.denote (decodeRecords ops (payloadWords t a M cache J N theta rows s j)) = _
  simp only [payloadWords,hh,ite_true]
  rw [←originStored_data ops u J hu hJ]
  change (constantStored _ u J _).denote = _
  rw [constantStored_denote]
  have hz : ops.decode (RingProgram.modelProgram t a M cache).zeroRun.1 = 0 := by
    rw [← RingProgram.modelRing_program t ht hd a M cache]
    exact ops.zero_correct
  have ho : ops.decode (RingProgram.modelProgram t a M cache).oneRun.1 = 1 := by
    rw [← RingProgram.modelRing_program t ht hd a M cache]
    exact ops.one_correct
  cases hb : (s 575).getD j false
  · simpa only [hb,Bool.false_eq_true,ite_false] using
      congrArg (fun c => canonical u J (atom (Index.origin : Index (Fin rows.length)) c)) hz
  · simpa only [hb,ite_true] using
      congrArg (fun c => canonical u J (atom (Index.origin : Index (Fin rows.length)) c)) ho

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
