import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSingle
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutFactorBounds

namespace OAI.Algorithms

/-! Polynomial bit-size envelopes for the actual per-row scope computation. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
open SubexponentialSAT.SubexpLayoutConstructionBounds

abbrev natBits (xs : List ℕ) := Encoding.encodeList Encoding.encodeNat xs

theorem natBits_append_length (xs ys : List ℕ) :
    (natBits (xs++ys)).length+1=(natBits xs).length+(natBits ys).length := by
  induction xs with
  | nil => simp [natBits,Encoding.encodeList,Nat.add_comm]
  | cons x xs ih =>
      simp only [List.cons_append,natBits,Encoding.length_encodeList_cons] at ih ⊢
      omega

theorem natBits_member_le (xs : List ℕ) (c : ℕ) (hc : c ∈ xs) :
    c+1 ≤ (natBits xs).length := by
  induction xs with
  | nil => simp at hc
  | cons x xs ih =>
      simp only [List.mem_cons] at hc
      simp only [natBits,Encoding.length_encodeList_cons,Encoding.length_encodeNat]
      rcases hc with rfl | hc
      · omega
      · have h := ih hc
        simp only [natBits] at h
        omega

theorem mergedCodes_cons (term : Term) (terms : List Term) :
    mergedCodes (term::terms)=mergedCodes terms++term.2 := by
  simp [mergedCodes,List.flatMap_append]

theorem merged_wire_le (terms : List Term) :
    (natBits (mergedCodes terms)).length ≤ (Encoding.encodeList payload terms).length := by
  induction terms with
  | nil => simp [mergedCodes,natBits,Encoding.encodeList]
  | cons term terms ih =>
      rw [mergedCodes_cons]
      have ha := natBits_append_length (mergedCodes terms) term.2
      simp only [natBits] at ih ha ⊢
      simp only [Encoding.length_encodeList_cons,payload,List.length_append,Encoding.length_frame]
      omega

theorem scope_budget_le (codes : List ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hwire : (natBits codes).length ≤ S) :
    SubexpScopeProducer.budget [true] codes ≤ scopeProgramBound S := by
  have hcodes : codes.length ≤ S := (Nat.le_of_succ_le (Encoding.length_encodeList_lower _ codes)).trans hwire
  have hindex : ∀ code ∈ codes, code/2 ≤ S := by
    intro code hc
    have h := (natBits_member_le codes code hc).trans hwire
    exact (Nat.div_le_self _ _).trans (by omega)
  have hchunk : ∀ code ∈ codes, SubexpChunkRecordMap.chunk [true] code ≤ S := by
    intro code hc
    exact (Nat.div_le_self _ _).trans (hindex code hc)
  have hrecord : ∀ w ∈ codes.map Encoding.encodeNat, w.length ≤ 2*S := by
    intro w hw
    obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hw
    have hh := (natBits_member_le codes code hc).trans hwire
    rw [Encoding.length_encodeNat]
    omega
  have hcallback : ∀ w ∈ codes.map Encoding.encodeNat,
      SubexpChunkRecordMap.callbackCost [true] w ≤ scopeCallbackBound S := by
    intro w hw
    obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hw
    have hb := literal_budget_le 1 (code/2) S hS (hindex code hc)
    have hm := hchunk code hc
    simp only [SubexpChunkRecordMap.callbackCost,Encoding.length_encodeNat,Nat.add_sub_cancel,
      SubexpChunkRecordMap.mappedBits_encodeNat,List.length_cons,List.length_nil,Nat.zero_add]
    unfold scopeCallbackBound
    omega
  have hr := records_budget_le (SubexpChunkRecordMap.callbackCost [true])
    (codes.map Encoding.encodeNat) (2*S) (scopeCallbackBound S) hrecord hcallback
  simp only [List.length_map] at hr
  have hr' : RecordPrograms.budget (SubexpChunkRecordMap.callbackCost [true])
      (codes.map Encoding.encodeNat) ≤ S*(12*S+scopeCallbackBound S+7) := by
    rw [show 6*(2*S)=12*S by omega] at hr
    exact hr.trans (Nat.mul_le_mul_right _ hcodes)
  have hm := Encoding.length_encodeList_upper Encoding.encodeNat
    (codes.map (SubexpChunkRecordMap.chunk [true])) (S+1) (by
      intro j hj
      obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hj
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right (hchunk code hc) 1)
  simp only [List.length_map] at hm
  have hm' : (Encoding.encodeList Encoding.encodeNat
      (codes.map (SubexpChunkRecordMap.chunk [true]))).length ≤ mappedScopeBytesBound S :=
    hm.trans (by unfold mappedScopeBytesBound; gcongr)
  change 5+RecordPrograms.budget (SubexpChunkRecordMap.callbackCost [true])
    (codes.map Encoding.encodeNat)+10*_+120*(_+1)^2 ≤ _
  unfold scopeProgramBound
  gcongr

theorem single_cost_le (terms : List Term) :
    Single.cost terms ≤ 11+46*(Encoding.encodeList payload terms).length+
      scopeProgramBound (Encoding.encodeList payload terms).length := by
  have hm := merged_wire_le terms
  have hp := Encoding.length_encodeList_lower payload terms
  have hs := scope_budget_le (mergedCodes terms) (Encoding.encodeList payload terms).length (by omega) hm
  have hf := Flatten.cost_le (terms.map payload)
  have he : Encoding.encodeList id (terms.map payload)=Encoding.encodeList payload terms := by
    clear hm hp hs hf
    induction terms with
    | nil => rfl
    | cons t ts ih => simp [Encoding.encodeList,ih]
  rw [he] at hf
  unfold Single.cost
  simp only [natBits] at hm
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
