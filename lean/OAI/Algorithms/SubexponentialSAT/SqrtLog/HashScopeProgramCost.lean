import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram

namespace OAI.Algorithms

/-! One ordinary polynomial in represented input bytes bounds the complete
scope-table producer, including outer parsing, framing, and final reversal. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
open SubexponentialSAT.SubexpLayoutConstructionBounds

theorem scopeProgramBound_mono {S T : ℕ} (h : S ≤ T) :
    scopeProgramBound S ≤ scopeProgramBound T := by
  unfold scopeProgramBound scopeCallbackBound literalBound mappedScopeBytesBound
    SubexpLiteralChunkProgram.budget
  gcongr

theorem scope_wire_le (terms : List Term) (S : ℕ)
    (h : (Encoding.encodeList payload terms).length ≤ S) :
    (Outer.scopeBytes terms).length ≤ mappedScopeBytesBound S := by
  have hm := (merged_wire_le terms).trans h
  have hl : (scope terms).length ≤ S := (SubexpScopeProducer.scope_length_le _ _).trans
    ((Nat.le_of_succ_le (Encoding.length_encodeList_lower Encoding.encodeNat (mergedCodes terms))).trans hm)
  have hv : ∀ v ∈ scope terms, v+1 ≤ S+1 := by
    intro v hv
    obtain ⟨term,ht,code,hc,rfl⟩ := (mem_scope terms v).mp hv
    have hc' : code∈mergedCodes terms := (mem_mergedCodes terms code).mpr ⟨term,ht,hc⟩
    have hb := (natBits_member_le (mergedCodes terms) code hc').trans hm
    have hd := Nat.div_le_self code 2
    omega
  have hw := Encoding.length_encodeList_upper Encoding.encodeNat (scope terms) (S+1)
    (by intro v hv'; simpa only [Encoding.length_encodeNat] using hv v hv')
  exact hw.trans (by unfold mappedScopeBytesBound; gcongr)

namespace Outer

def rowCostBound (S : ℕ) : ℕ :=
  55*S+scopeProgramBound S+8*mappedScopeBytesBound S+50

def polynomialBound (S : ℕ) : ℕ :=
  8+S*rowCostBound S+10*(1+(2*mappedScopeBytesBound S+2)*S)

theorem loopCost_le (rows : Rows) (S : ℕ)
    (h : ∀ row∈rows, (rowBits row).length ≤ S) :
    loopCost rows ≤ rows.length*rowCostBound S := by
  induction rows with
  | nil => simp [loopCost]
  | cons row rows ih =>
      have hr := h row (by simp)
      have ht := ih (fun x hx => h x (by simp [hx]))
      have hs := (single_cost_le row).trans (show
          11+46*(rowBits row).length+scopeProgramBound (rowBits row).length ≤
          11+46*S+scopeProgramBound S by
        exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 46 hr) 11)
          (scopeProgramBound_mono hr))
      have hw := scope_wire_le row S hr
      simp only [loopCost,List.length_cons,Nat.add_mul,Nat.one_mul]
      unfold callbackCost rowCostBound scopeBytes rowBits at *
      omega

theorem input_row_length (rows : Rows) (row : List Term) (h : row∈rows) :
    (rowBits row).length ≤ (inputBits rows).length := by
  induction rows with
  | nil => simp at h
  | cons head tail ih =>
      simp only [List.mem_cons] at h
      have he : (inputBits (head::tail)).length=
          2*(rowBits head).length+2+(inputBits tail).length := by
        simp [inputBits,Encoding.encodeList,Encoding.length_frame]
        omega
      rw [he]
      rcases h with rfl | h
      · omega
      · have ht := ih h; omega

theorem cost_le (rows : Rows) : cost rows ≤ polynomialBound (inputBits rows).length := by
  let S := (inputBits rows).length
  have hrows : rows.length ≤ S := by
    have h := Encoding.length_encodeList_lower id (rows.map rowBits)
    simpa [S, inputBits] using Nat.le_of_succ_le h
  have hr : ∀ row∈rows, (rowBits row).length ≤ S := input_row_length rows
  have hl := (loopCost_le rows S hr).trans (Nat.mul_le_mul_right _ hrows)
  have hw := Encoding.length_encodeList_upper id (rows.map scopeBytes) (mappedScopeBytesBound S) (by
    intro bits hb
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hb
    exact scope_wire_le row S (hr row hrow))
  simp only [List.length_map] at hw
  have hw' : (scopeBits rows).length ≤ 1+(2*mappedScopeBytesBound S+2)*S :=
    hw.trans (by gcongr)
  unfold cost polynomialBound
  dsimp [S] at *
  omega

end Outer
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
