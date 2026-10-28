import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsPayload

namespace OAI.Algorithms

/-! Per-call source witnesses suffice for a valid typed payload and its exact
incidence semantics. No common byte representation across source calls is
required. Length transports below only identify equal ambient dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly

open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LeafProgram.NativeSemantics
open LeafProgram.AssignmentSemantics (good_of_decoded_valid)

 def castEntries {m n B d : ℕ} (h : m=n)
    (entries : List (MomentsProgram.Product.Entry m B d)) :
    List (MomentsProgram.Product.Entry n B d) := h ▸ entries

noncomputable def castJet {R : Type*} [CommRing R] {m n : ℕ}
    (h : m=n) (P : Squarefree.Jet (Fin m) R) : Squarefree.Jet (Fin n) R := h ▸ P

 theorem castEntries_bits {m n B d : ℕ} (h : m=n)
    (entries : List (MomentsProgram.Product.Entry m B d)) :
    PerturbationProgram.dictionaryBits (castEntries h entries) =
      PerturbationProgram.dictionaryBits entries := by subst n; rfl

 theorem castEntries_good {m n B d u J : ℕ} (h : m=n)
    (entries : List (MomentsProgram.Product.Entry m B d))
    (he : Good Finset.univ u J entries) :
    Good Finset.univ u J (castEntries h entries) := by subst n; exact he

 theorem castEntries_denote {R : Type*} [CommRing R] {m n B d : ℕ} (h : m=n)
    (f : RingProgram.Code (Word B) d → R)
    (entries : List (MomentsProgram.Product.Entry m B d)) :
    rawDenote f (castEntries h entries) = castJet h (rawDenote f entries) := by subst n; rfl

/-- Typed low output for any actual array witness of the required length. -/
theorem lowOutput_realizes (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (hlen : rows.length=n) :
    ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 t) d),
      lowOutput t a M cache J N theta rows [] = PerturbationProgram.dictionaryBits entries ∧
      Good Finset.univ u J entries ∧
      rawDenote (RingProgram.modelRing t ht hd a M cache).decode entries =
        castJet hlen (nativeStored t ht hd a M cache u J N hu hJ theta rows).denote := by
  let words := outputWords (RingProgram.modelProgram t a M cache) J theta
    (PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)
  have hv : Good Finset.univ u J words := by
    apply good_of_decoded_valid Finset.univ (RingProgram.modelRing t ht hd a M cache).decode
    · exact outputWords_valid (RingProgram.modelRing t ht hd a M cache) u J hu hJ _ _ _
    · exact outputWords_nodup _ _ _ _ _
  refine ⟨castEntries hlen words,?_,castEntries_good hlen words hv,?_⟩
  · rw [castEntries_bits]
    exact lowOutput_dictionary t a M cache J N theta rows
  · rw [castEntries_denote]
    rfl

/-- Exact branch-sensitive semantics, retaining each low call's own source
witness and its property Rows. The high branch needs no source witness. -/
theorem payloadRelation_realizes (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N n : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (Rows : ℕ → List (Fixed.Array (baseWidth 3 t) d N) → Prop)
    (s : OuterStore) (j : ℕ) (payload : List Bool)
    (hc : (s 546).length=n)
    (hz : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (ho : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hr : payloadRelation t a M cache J N theta n Rows s j payload) :
    ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 t) d),
      payload=PerturbationProgram.dictionaryBits entries ∧ Good Finset.univ u J entries ∧
      (if (s 574).getD j false then
        rawDenote (RingProgram.modelRing t ht hd a M cache).decode entries =
          Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin
            (if (s 575).getD j false then (1 : a.O t) else 0))
      else ∃ xs : List (Fixed.Array (baseWidth 3 t) d N), ∃ hx : xs.length=n, Rows j xs ∧
        rawDenote (RingProgram.modelRing t ht hd a M cache).decode entries =
          castJet ((pairChoice_length xs (s 546) (hx.trans hc.symm)).trans hx)
            (nativeStored t ht hd a M cache u J N hu hJ theta (pairChoice xs (s 546))).denote) := by
  cases hh : (s 574).getD j false
  · simp only [payloadRelation,hh,Bool.false_eq_true,ite_false] at hr
    obtain ⟨xs,hx,hRows,hpayload⟩ := hr
    have hlen := (pairChoice_length xs (s 546) (hx.trans hc.symm)).trans hx
    obtain ⟨entries,hbits,hgood,hden⟩ := lowOutput_realizes t ht hd a M cache u J N n hu hJ
      theta (pairChoice xs (s 546)) hlen
    refine ⟨entries,hpayload.trans hbits,hgood,?_⟩
    simp only [Bool.false_eq_true,ite_false]
    exact ⟨xs,hx,hRows,hden⟩
  · simp only [payloadRelation,hh,ite_true] at hr
    let ops := RingProgram.modelRing t ht hd a M cache
    let c := if (s 575).getD j false then (RingProgram.modelProgram t a M cache).oneRun.1
      else (RingProgram.modelProgram t a M cache).zeroRun.1
    let entries : List (MomentsProgram.Product.Entry n (baseWidth 3 t) d) :=
      [(Squarefree.Index.origin,c)]
    have hg : Good Finset.univ u J entries := by
      constructor
      · intro e he
        simp only [entries,List.mem_singleton] at he
        subst e
        simp [MomentsProgram.Product.ValidKey,Squarefree.Index.origin,
          Squarefree.Index.Kept,Squarefree.Index.Valid,hu,hJ]
      · simp [entries,Squarefree.Sparse.keys]
    refine ⟨entries,?_,hg,?_⟩
    · rw [hr]
      have he := origin_dictionary n c
      cases hb : (s 575).getD j false <;>
        simpa only [entries,c,hb,Bool.false_eq_true,ite_false,ite_true,hz,ho] using he
    · simp only [ite_true]
      change rawDenote ops.decode entries = _
      have he : rawDenote ops.decode entries =
          Squarefree.canonical u J (Squarefree.Sparse.atom Squarefree.Index.origin (ops.decode c)) := by
        change Squarefree.Sparse.denote (PerturbationProgram.decodeRecords ops entries) = _
        rw [show PerturbationProgram.decodeRecords ops entries =
          (PerturbationProgram.constantStored (Finset.univ : Finset (Fin n)) u J (ops.decode c)).data from
            (originStored_data ops u J hu hJ c).symm]
        exact PerturbationProgram.constantStored_denote (Finset.univ : Finset (Fin n)) u J (ops.decode c)
      rw [he]
      cases hb : (s 575).getD j false
      · have hz : ops.decode (RingProgram.modelProgram t a M cache).zeroRun.1 = 0 := by
          rw [← RingProgram.modelRing_program t ht hd a M cache]
          exact ops.zero_correct
        simpa only [c,hb,Bool.false_eq_true,ite_false] using
          congrArg (fun x => Squarefree.canonical u J
            (Squarefree.Sparse.atom (Squarefree.Index.origin : Squarefree.Index (Fin n)) x)) hz
      · have ho : ops.decode (RingProgram.modelProgram t a M cache).oneRun.1 = 1 := by
          rw [← RingProgram.modelRing_program t ht hd a M cache]
          exact ops.one_correct
        simpa only [c,hb,ite_true] using
          congrArg (fun x => Squarefree.canonical u J
            (Squarefree.Sparse.atom (Squarefree.Index.origin : Squarefree.Index (Fin n)) x)) ho

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
