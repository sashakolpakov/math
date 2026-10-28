import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramMarkedTable

namespace OAI.Algorithms

/-! A fixed polynomial envelope for raw references plus the optional original
marked clause. The size parameter bounds stored byte lengths and row/slot counts. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.SubexpLayoutConstructionBounds

def weightedBytesBound (S : ℕ) : ℕ := 1+(6*S+4)*S

def assemblyBound (S : ℕ) : ℕ :=
  3+S*(HashInputProgram.Loop.termBudget S S S S S S+4)

def rowCostBound (S : ℕ) : ℕ :=
  12*S*S+assemblyBound S+31+46*weightedBytesBound S+
    scopeProgramBound (weightedBytesBound S)+8*mappedScopeBytesBound (weightedBytesBound S)+37

def optionalCostBound (S : ℕ) : ℕ :=
  2*S+10+23*S+scopeProgramBound S+8*mappedScopeBytesBound (weightedBytesBound S)+51

def polynomialBound (S : ℕ) : ℕ :=
  10+S*rowCostBound S+optionalCostBound S+
    10*(1+(2*mappedScopeBytesBound (weightedBytesBound S)+2)*(S+1))

theorem clause_wire_le (clauses : List (List Bool)) (i : Fin clauses.length) :
    clauses[i.val].length ≤ (Encoding.encodeList id clauses).length :=
  HashInputProgram.Loop.original_payload_length_le clauses _ (List.getElem_mem i.isLt)

theorem weighted_wire_le (t d : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (row : List (Fin clauses.length × ZMod 3)) (S : ℕ)
    (hrow : row.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    (Encoding.encodeList payload (FromTuple.interpretedTerms (clauses := clauses) t d codes row)).length ≤
      weightedBytesBound S := by
  rw [FromTuple.interpreted_payload t d clauses codes hc row]
  have h := Encoding.length_encodeList_upper id (row.map (HashInputProgram.Loop.payload t d clauses)) (3*S+1) (by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    have hclause := (clause_wire_le clauses a.1).trans hmaster
    simp only [id_eq,HashInputProgram.Loop.payload,List.length_append,Encoding.length_frame,
      HashInputProgram.Loop.flat_length]
    omega)
  simp only [List.length_map] at h
  exact h.trans (calc
    _ ≤ 1+(2*(3*S+1)+2)*S := by gcongr
    _ = weightedBytesBound S := by unfold weightedBytesBound; ring)

theorem assembly_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (count S : ℕ) (hn : count ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hc : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    HashInputProgram.Loop.uniformBudget t d b modulus clauses count ≤ assemblyBound S := by
  unfold HashInputProgram.Loop.uniformBudget assemblyBound
  gcongr
  unfold HashInputProgram.Loop.termBudget HashInputProgram.LoopDecode.budget
  gcongr

theorem marked_wire_le (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (i : Fin clauses.length) (S : ℕ) (hS : 1 ≤ S)
    (hmaster : (Encoding.encodeList id clauses).length ≤ S) :
    (Marked.scopeBits (codes i)).length ≤ mappedScopeBytesBound (weightedBytesBound S) := by
  have hw : (Encoding.encodeList Encoding.encodeNat (codes i)).length ≤ S := by
    rw [← hc i]
    exact (clause_wire_le clauses i).trans hmaster
  have hp : (Encoding.encodeList payload [([],codes i)]).length ≤ weightedBytesBound S := by
    simp only [payload,List.length_append,Encoding.length_frame,
      List.length_nil,Encoding.encodeList,List.length_cons]
    have hss : S ≤ S*S := by simpa using Nat.mul_le_mul_left S hS
    unfold weightedBytesBound
    nlinarith
  have hh := scope_wire_le [([],codes i)] (weightedBytesBound S) hp
  simpa [Outer.scopeBytes,scope,mergedCodes,Marked.scopeBits] using hh

theorem row_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (row : List (Fin clauses.length × ZMod 3)) (S : ℕ)
    (hrow : row.length ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hclauses : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    6*(RawTable.rowBits b row).length+RawTable.callbackCost t d b modulus clauses codes row+7 ≤ rowCostBound S := by
  have hw := weighted_wire_le t d clauses codes hc row S hrow hmaster hweight
  have hs := single_cost_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row)
  have hsp := scopeProgramBound_mono hw
  have hsw := scope_wire_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row) (weightedBytesBound S) hw
  have ha := assembly_cost_le t d b modulus clauses row.length S hrow hb hm hclauses hmaster hweight
  have hr : (RawTable.rowBits b row).length ≤ S*S := by
    change (CodeRowsProgram.rowPayload b clauses.length row).length ≤ S*S
    rw [CodeRowsProgram.rowPayload_length]
    exact Nat.mul_le_mul hrow hb
  unfold rowCostBound RawTable.callbackCost FromTuple.cost RawTable.scopeBytes Outer.scopeBytes at *
  simp only [Nat.mul_assoc] at *
  omega

theorem loop_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (S : ℕ)
    (hrows : ∀ row∈rows, row.length ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hclauses : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    RawTable.loopCost t d b modulus clauses codes rows ≤ rows.length*rowCostBound S := by
  induction rows with
  | nil => simp [RawTable.loopCost]
  | cons row rows ih =>
      have hh := row_cost_le t d b modulus clauses codes hc row S (hrows row (by simp)) hb hm hclauses hmaster hweight
      have ht := ih (fun r hr => hrows r (by simp [hr]))
      simp only [RawTable.loopCost,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem optional_cost_le (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (mark : Option (Fin clauses.length)) (index : List Bool) (S : ℕ) (hS : 1 ≤ S)
    (hindex : index.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S) :
    Marked.optionalCost clauses codes mark index ≤ optionalCostBound S := by
  cases mark with
  | none => simp [Marked.optionalCost,optionalCostBound]; omega
  | some i =>
      have hwire : (natBits (codes i)).length ≤ S := by
        change (Encoding.encodeList Encoding.encodeNat (codes i)).length ≤ S
        rw [← hc i]
        exact (clause_wire_le clauses i).trans hmaster
      have hb := scope_budget_le (codes i) S hS hwire
      have hw := marked_wire_le clauses codes hc i S hS hmaster
      change 2*index.length+10+Marked.processCost clauses codes i ≤ optionalCostBound S
      unfold Marked.processCost optionalCostBound
      omega

theorem cost_le_polynomial (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) (index : List Bool)
    (S : ℕ) (hS : 1 ≤ S) (hn : rows.length ≤ S) (hrows : ∀ row∈rows, row.length ≤ S)
    (hb : b ≤ S) (hm : modulus.length ≤ S) (hclauses : clauses.length ≤ S)
    (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) (hindex : index.length ≤ S) :
    cost t d b modulus clauses codes rows mark index ≤ polynomialBound S := by
  have hl := (loop_cost_le t d b modulus clauses codes hc rows S hrows hb hm hclauses hmaster hweight).trans
    (Nat.mul_le_mul_right (rowCostBound S) hn)
  have ho := optional_cost_le clauses codes hc mark index S hS hindex hmaster
  have hwords : ∀ w∈scopeWords (clauses := clauses) t d codes rows mark,
      w.length ≤ mappedScopeBytesBound (weightedBytesBound S) := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hw
      exact scope_wire_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row) _
        (weighted_wire_le t d clauses codes hc row S (hrows row hr) hmaster hweight)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact marked_wire_le clauses codes hc i S hS hmaster
  have hlen : (scopeWords (clauses := clauses) t d codes rows mark).length ≤ S+1 := by
    cases mark <;> simp [scopeWords] <;> omega
  have hout := Encoding.length_encodeList_upper id (scopeWords (clauses := clauses) t d codes rows mark)
    (mappedScopeBytesBound (weightedBytesBound S)) hwords
  have hout' : (outputBits (clauses := clauses) t d codes rows mark).length ≤
      1+(2*mappedScopeBytesBound (weightedBytesBound S)+2)*(S+1) :=
    hout.trans (by gcongr)
  unfold cost polynomialBound
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
