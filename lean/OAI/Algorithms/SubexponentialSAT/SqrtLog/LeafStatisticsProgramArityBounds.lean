import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramArity

namespace OAI.Algorithms

/-! Polynomial cost in the actual serialized scope input and mask length. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem scopeBudget_le (mask : List Bool) (scope : List ℕ) :
    scopeBudget mask scope ≤ (16*(mask.length+1)+17)*
      ((Encoding.encodeList Encoding.encodeNat scope).length+1) := by
  have h := RecordPrograms.program_budget_le_input
    (fun _ => 16*(mask.length+1)) (scope.map Encoding.encodeNat) 0 (16*(mask.length+1))
    (by intro bits hb; simp)
  simpa [scopeBudget,ProgramEncoding.encodeRecords,SubexpScopeCountSetup.encode_scope] using h

theorem cost_le (mask : List Bool) (scope : List ℕ) :
    cost mask (Encoding.encodeList Encoding.encodeNat scope) ≤
      (16*(mask.length+1)+42)*((Encoding.encodeList Encoding.encodeNat scope).length+1) := by
  have hb := scopeBudget_le mask scope
  have hl := Encoding.length_encodeList_lower Encoding.encodeNat scope
  simp only [cost,decoded_encode]
  nlinarith

theorem totalBudget_le (mask : List Bool) (scopes : List (List ℕ)) :
    4+RecordPrograms.budget (cost mask) (scopes.map (Encoding.encodeList Encoding.encodeNat)) ≤
      (32*(mask.length+1)+101)*
        ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes).length+1) := by
  have h := RecordPrograms.program_budget_le_input (cost mask)
    (scopes.map (Encoding.encodeList Encoding.encodeNat))
    (16*(mask.length+1)+42) (16*(mask.length+1)+42)
    (by
      intro bits hb
      obtain ⟨scope,hs,rfl⟩ := List.mem_map.mp hb
      have hc := cost_le mask scope
      nlinarith)
  have hencode : ∀ xs : List (List ℕ), ProgramEncoding.encodeRecords
      (xs.map (Encoding.encodeList Encoding.encodeNat)) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xs := by
    intro xs
    change Encoding.encodeList id (xs.map (Encoding.encodeList Encoding.encodeNat)) = _
    induction xs with
    | nil => rfl
    | cons scope scopes ih => simp [Encoding.encodeList,ih]
  rw [hencode] at h
  convert h using 1 ; ring

theorem program_primitive (r : Fin 10 → Bool) (mask : List Bool) (scopes : List (List ℕ))
    (hv : ∀ scope ∈ scopes, ∀ v ∈ scope, v < mask.length) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * ((32*(mask.length+1)+101)*
        ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes).length+1)))
      (primitiveCfg program ((RecordPrograms.state ports (state r mask [] [] [] 0 0)
        false true false (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) scopes) []).withPC
        (some program.entry)))
      (primitiveCfg program ((state rf mask [] [] [] (arity mask scopes 0) scopes.length).withPC none)) := by
  obtain ⟨rf,hr⟩ := program_runsIn r mask scopes hv
  exact ⟨rf,BitProgram.primitive_execution program (hr.mono (totalBudget_le mask scopes))⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
