import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStoredPayload

namespace OAI.Algorithms

/-! Actual perturbation dictionaries satisfy the assignment evaluator's raw
Good predicate. Validity is ambient: zero records at fixed-coordinate keys
are retained and need not have structurally free support. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open NativeSemantics

 theorem good_of_decoded_valid {R : Type*} [CommRing R] {n B d u J : ℕ}
    (vars : Finset (Fin n)) (f : RingProgram.Code (Word B) d → R)
    (entries : List (MomentsProgram.Product.Entry n B d))
    (hv : Squarefree.Sparse.ValidData vars u J (MomentsProgram.Dictionary.denoteTable f entries))
    (hn : (Squarefree.Sparse.keys entries).Nodup) : Good vars u J entries := by
  refine ⟨?_,hn⟩
  intro a ha
  apply hv a.1
  simpa only [Squarefree.Sparse.keys,MomentsProgram.Dictionary.denoteTable,
    List.map_map,Function.comp_def] using
    (List.mem_map.mpr ⟨a,ha,rfl⟩ : a.1 ∈ entries.map Prod.fst)

 theorem payload_good (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (s : PerturbationAssembly.OuterStore) (j : ℕ) :
    Good Finset.univ u J (PerturbationAssembly.payloadWords t a M cache J N theta rows s j) := by
  apply good_of_decoded_valid Finset.univ (RingProgram.modelRing t ht hd a M cache).decode
  · exact PerturbationAssembly.payloadWords_valid t ht hd a M cache u J N hu hJ theta rows s j
  · exact PerturbationAssembly.payloadWords_nodup t a M cache J N theta rows s j

 theorem payload_rawDenote (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (s : PerturbationAssembly.OuterStore) (j : ℕ) :
    rawDenote (RingProgram.modelRing t ht hd a M cache).decode
      (PerturbationAssembly.payloadWords t a M cache J N theta rows s j) =
    (PerturbationAssembly.payloadStored t ht hd a M cache u J N hu hJ theta rows s j).denote := rfl

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
