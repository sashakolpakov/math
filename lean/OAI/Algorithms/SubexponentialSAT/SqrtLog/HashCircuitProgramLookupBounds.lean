import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramIncidence

namespace OAI.Algorithms

/-! Explicit polynomial byte and scan bounds for the selected incidence table.
All dictionary payloads are still physically copied and scanned. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.LookupBounds

theorem records_length (entries : List (List Bool × List Bool)) (W P : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hp : ∀ a ∈ entries, a.2.length ≤ P) :
    (Squarefree.Program.lookupRecords entries).length ≤ entries.length*(2*W+2*P+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords]
  | cons a entries ih =>
    have ha := hk a (by simp)
    have hb := hp a (by simp)
    have ht := ih (fun x hx => hk x (by simp [hx])) (fun x hx => hp x (by simp [hx]))
    simp only [Squarefree.Program.lookupRecords,Subexp.SelectorProgram.rawRecords,
      List.flatMap_cons,List.length_append,Encoding.length_frame,List.length_cons] at *
    nlinarith

theorem fetch_budget (key : List Bool) (entries : List (List Bool × List Bool)) (W P : ℕ)
    (hq : key.length ≤ W) (hk : ∀ a ∈ entries, a.1.length ≤ W)
    (hp : ∀ a ∈ entries, a.2.length ≤ P) :
    literalFetchBudget key entries ≤ entries.length*(44*W+31*P+58)+2*W+16 := by
  have hr := records_length entries W P hk hp
  have hs := Squarefree.Program.lookupBudget_bound key entries W P hk hp
  dsimp only [literalFetchBudget]
  nlinarith

theorem incidence_entries_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) :
    (incidenceEntries payload i).length = n := by
  simp [incidenceEntries]

theorem incidence_key_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) :
    ∀ a ∈ incidenceEntries payload i, a.1.length ≤ n := by
  intro a ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  simp only [Encoding.length_encodeNat]
  exact v.isLt

theorem incidence_payload_length {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (P : ℕ)
    (hp : ∀ v, (payload i v).length ≤ P) :
    ∀ a ∈ incidenceEntries payload i, a.2.length ≤ P := by
  intro a ha
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  exact hp v

theorem incidence_fetch_budget {I : Type*} {n : ℕ}
    (payload : I → Fin n → List Bool) (i : I) (P : ℕ)
    (hp : ∀ v, (payload i v).length ≤ P) (v : Fin n) :
    literalFetchBudget (Encoding.encodeNat v.val) (incidenceEntries payload i) ≤
      n*(44*n+31*P+58)+2*n+16 := by
  have hq : (Encoding.encodeNat v.val).length ≤ n := by
    simpa only [Encoding.length_encodeNat, Nat.succ_le_iff] using v.isLt
  simpa only [incidence_entries_length] using fetch_budget (Encoding.encodeNat v.val)
    (incidenceEntries payload i) n P hq (incidence_key_length payload i)
      (incidence_payload_length payload i P hp)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.LookupBounds

end OAI.Algorithms
