import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredBytes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLow

namespace OAI.Algorithms

/-! The actual low-variable worker's byte output, including its internally
computed beta, is the unnormalized Stored incidence dictionary. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem originKey_eq_encodeIndex (n : ℕ) :
    originKey n = encodeIndex (Index.origin : Index (Fin n)) := by
  simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits,
    encodeIndex,Index.origin,encodeMask,Encoding.encodeNat]

theorem origin_dictionary {B d : ℕ} (n : ℕ) (beta : Coeff B d) :
    Encoding.frame (originKey n) ++ Encoding.frame (RingProgram.flat beta) =
      dictionaryBits [((Index.origin : Index (Fin n)),beta)] := by
  simp [dictionaryBits,originKey_eq_encodeIndex]

theorem lowOutput_dictionary (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) :
    lowOutput t a M cache J N theta rows [] =
      dictionaryBits (outputWords (RingProgram.modelProgram t a M cache) J theta
        (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
        (fun v : Fin rows.length => rows[v].1.val)) := by
  have he : (rows.map Prod.fst).zipIdx 0 =
      List.ofFn (fun v : Fin rows.length => (rows[v].1,v.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.getElem_zipIdx]
  have hr : scanRecords (RingProgram.modelProgram t a M cache) J rows.length N
      theta 0 (rows.map Prod.fst) =
      (List.ofFn fun v : Fin rows.length => coefficientRecords v 1
        (shiftedValue (RingProgram.modelProgram t a M cache) J theta rows[v].1.val).val.tail).flatten := by
    unfold scanRecords
    rw [he,List.flatMap_def,List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext v
    simp only [Function.comp_apply,dite_eq_left v.isLt]
  rw [lowOutput,List.append_nil,origin_dictionary,rowsResult_dictionary,hr]
  simp only [outputWords,rawWords,List.reverse_cons]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
