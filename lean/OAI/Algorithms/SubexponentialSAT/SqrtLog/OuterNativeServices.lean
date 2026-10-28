import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeTrial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeHistoryServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeRuntimeAt

namespace OAI.Algorithms

/-! Concrete native history services for all original and trial rows. Every
candidate, including a losing candidate, has its actual Origin and optional
mark reconstructed from the exact selector history. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram HashSelectProgram
open LeafScopeResourceBounds
noncomputable section

 theorem native_history_services {n B k qi : ℕ} (F : OuterQuery.Formula n)
    (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length) (hn : 2 ≤ n)
    (hk : ∀C∈F,C.length ≤ k) (hcount : F.length ≤ n*B)
    (hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F))
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (code : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (hrows : a.stacks 777=candidateEncoding (OuterQuery.initial F a s code))
    (W L Q : ℕ) (hw : SubexpSetupStorage.WordBound W a)
    (hL : W+CounterPrograms.value (a.stacks 774)*
      (2*(CounterPrograms.value (a.stacks 773)*(a.stacks 768).length)+2)+
      CounterPrograms.value (a.stacks 773)*(a.stacks 768).length ≤ L)
    (runtime : RuntimeAt n k B qi (7*L+(formulaRecords F).length+2) Q) :
    ∃svc : HistoryServices (formulaClauses F) (LeafOuterNative.mass k)
      (LeafOuterNative.acceptedCount k) a (OuterQuery.initial F a s code),
      svc.massSteps=F.length*Q+LeafOuterNative.overhead L F.length
        (LeafParametersProgram.precision n F.length) (Q+1)+64 ∧
      svc.countSteps=5000*(L+Q+1) ∧ svc.countBits=Q+1 := by
  let score := massScore (formulaClauses F) (a.stacks 768).length
  have hdepth : CounterPrograms.value (a.stacks 773)=
      SparseCode.distanceDenom (formulaRecords F).length B := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.depth
  have hrounds : CounterPrograms.value (a.stacks 774)=
      HashSelect.loopCap n (formulaRecords F).length := by
    simpa only [CounterPrograms.value_eq_toNat] using ha.rounds
  apply historyServices_of_native_queries k (formulaClauses F) a
    (by simpa only [formulaRecords_length] using ha)
    (OuterQuery.initial F a s code) hrows W L Q hw (by omega)
  · intro seed rest hf frame hframe round hr current hcurrent bits best queue regs hb
    have hfamily := hf
    rw [hdepth] at hfamily
    have hround : round < HashSelect.loopCap n (formulaRecords F).length := by
      simpa only [hrounds] using hr
    let selectedRows := iter (payloadNext score seed rest) round (OuterQuery.initial F a s code)
    let entry := OuterQuery.massInput current regs bits best queue
    have hsource : ∀i,LeafOuterNative.MassSource i → (entry.stacks i).length ≤ L := by
      intro i hi
      exact (massInput_sources_le hw hrows hframe hcurrent (Nat.le_of_lt hr)
        (family_payload_le a ha seed rest hf) regs bits best queue hb i hi).trans hL
    have info (mark : Option (Fin (formulaRecords F).length)) :=
      OuterQuery.trial_provenance F a frame current ha hformula (by omega) hm hk s code
        score seed rest hfamily round hround hframe hcurrent regs bits best queue hb mark
    have info' (mark : Option (Fin (formulaRecords F).length)) :
        let q := OuterQuery.query F a
          (OuterQuery.Count.payloadRows F (a.stacks 768).length hm (bits::selectedRows)) mark
        q.Valid ∧ ProducedQueryResources.ambient q=n ∧
          Nonempty (ProducedQueryResources.Origin q k B) ∧ OuterQuery.TrialWords q entry := by
      simpa only [OuterQuery.trialRows,OuterQuery.Count.payloadRows,trial,selectedRows,
        ha.width] using info mark
    have rt (mark : Option (Fin (formulaRecords F).length)) :=
      runtime.marked _ (info' mark).1 (info' mark).2.1
        (info' mark).2.2.1.some (by simpa only [OuterQuery.query_clause_count] using hcount)
        (trial_queryBytes_le (info' mark).2.2.2 hsource
          (query_index_length_le F a hm _ mark))
    exact bounded_trial_native F a ha (a.stacks 768).length L Q hm selectedRows bits hk hn
      entry (OuterQuery.massInput_worker ha.worker hframe hcurrent regs bits best queue)
      hsource
      (by rw [OuterQuery.massInput_outer hframe hcurrent regs bits best queue 782 (by omega)]; exact ha.clauses)
      (by rw [OuterQuery.massInput_outer hframe hcurrent regs bits best queue 785 (by omega)]; exact ha.ambient)
      (fun mark => (info' mark).2.2.2) (fun mark => (info' mark).1)
      (fun mark => (rt mark).1) (fun mark => (rt mark).2)
  · intro seed rest hf b hframe hworker hselected
    have hfamily := hf
    rw [hdepth] at hfamily
    let selectedRows := iter (payloadNext score seed rest)
      (CounterPrograms.value (a.stacks 774)) (OuterQuery.initial F a s code)
    have hselected' : b.stacks 777=candidateEncoding
        (selected score seed rest (OuterQuery.initial F a s code)
          (HashSelect.loopCap n (formulaRecords F).length)) := by
      simpa only [hrounds] using hselected
    have info := OuterQuery.final_provenance F a b ha hformula (by omega) hm hk s code score
      seed rest hfamily hframe hselected' none
    have info' :
        let q := OuterQuery.query F a
          (OuterQuery.Count.payloadRows F (a.stacks 768).length hm selectedRows) none
        q.Valid ∧ ProducedQueryResources.ambient q=n ∧
          Nonempty (ProducedQueryResources.Origin q k B) ∧ OuterQuery.FinalWords q b := by
      simpa only [OuterQuery.finalRows,OuterQuery.Count.payloadRows,selectedRows,hrounds,
        ha.width] using info
    have hs : ∀i,LeafOuterNative.AcceptedSource i → (b.stacks i).length ≤ L := by
      intro i hi
      exact (final_sources_le hw hrows hframe hselected
        (family_payload_le a ha seed rest hf) i hi).trans (by omega)
    have hbytes := final_queryBytes_le info'.2.2.2 (hs 784 (by simp [LeafOuterNative.AcceptedSource])) (hs 777 (by simp [LeafOuterNative.AcceptedSource]))
      (hs 782 (by simp [LeafOuterNative.AcceptedSource])) (hs 783 (by simp [LeafOuterNative.AcceptedSource])) (hs 785 (by simp [LeafOuterNative.AcceptedSource]))
      (query_index_length_le F a hm _ none)
    obtain ⟨facts,hbound⟩ := runtime.accepted _ info'.1 info'.2.1 info'.2.2.1.some (by simpa only [OuterQuery.query_clause_count] using hcount)
      (hbytes.trans (by omega))
    exact final_native F a ha (a.stacks 768).length Q hm selectedRows hk hn b hworker
      info'.2.2.2 info'.1 facts hbound

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
