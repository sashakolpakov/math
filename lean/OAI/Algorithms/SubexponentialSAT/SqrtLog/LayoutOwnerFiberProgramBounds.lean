import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Exact list-order specification, without reindexing the original owners. -/
theorem fiberIndices_eq_filter (query index : ℕ) (ps : List (ℕ × ℕ)) :
    fiberIndices query index ps =
      (((ps.zipIdx index).filter fun x => decide (x.1.1=query)).map Prod.snd) := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=query <;> simp [fiberIndices,h,ih]

theorem mem_fiberIndices_bounds (query index : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query index ps) :
    index ≤ i ∧ i < index+ps.length := by
  induction ps generalizing index with
  | nil => simp [fiberIndices] at hi
  | cons p ps ih =>
      by_cases h : p.1=query
      · simp only [fiberIndices,h,ite_true,List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · have hh := ih (index+1) hi
          simp only [List.length_cons]
          omega
      · simp only [fiberIndices,h,ite_false] at hi
        have hh := ih (index+1) hi
        simp only [List.length_cons]
        omega

theorem mem_fiberIndices_lt (query : ℕ) (ps : List (ℕ × ℕ))
    {i : ℕ} (hi : i ∈ fiberIndices query 0 ps) : i < ps.length := by
  have hh := mem_fiberIndices_bounds query 0 ps hi
  omega

theorem fiberIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (fiberIndices query index ps).length ≤ ps.length := by
  rw [fiberIndices_eq_filter]
  simpa using List.length_filter_le (fun x : (ℕ × ℕ) × ℕ => decide (x.1.1=query)) (ps.zipIdx index)

theorem encodeIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (encodeIndices (fiberIndices query index ps)).length ≤ ps.length*(index+ps.length+1) := by
  induction ps generalizing index with
  | nil => simp [fiberIndices,encodeIndices]
  | cons p ps ih =>
      have hh := ih (index+1)
      by_cases h : p.1=query <;>
        simp [fiberIndices,h,encodeIndices,Encoding.encodeNat] at * <;> nlinarith

def mass (ps : List (ℕ × ℕ)) : ℕ := (ps.map fun p => p.1+p.2).sum

theorem stream_length (ps : List (ℕ × ℕ)) :
    (stream ps).length=8*mass ps+24*ps.length+1 := by
  induction ps with
  | nil => simp [stream,Encoding.encodeList,mass]
  | cons p ps ih =>
      change (true::(Encoding.frame (pairPayload p.1 p.2)++stream ps)).length=_
      simp only [List.length_cons,List.length_append,Encoding.length_frame,pairPayload_length,ih]
      simp only [mass,List.map_cons,List.sum_cons]
      unfold mass at ih
      omega

theorem scanCost_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    scanCost query index ps ≤
      1+71*mass ps+ps.length*(9*query+7*index+7*ps.length+210) := by
  induction ps generalizing index with
  | nil => simp [scanCost,mass]
  | cons p ps ih =>
      have hh := ih (index+1)
      simp only [scanCost,callbackCost,pairPayload_length]
      simp only [mass,List.map_cons,List.sum_cons,List.length_cons]
      unfold mass at hh
      nlinarith

/-- Polynomial in the actual encoded source length and unary query size.
No list expansion or unit-cost arithmetic appears in the execution theorem. -/
theorem budget_polynomial (query : ℕ) (ps : List (ℕ × ℕ)) :
    budget query ps ≤ 1000*((stream ps).length+query+1)^2 := by
  have hL := stream_length ps
  have hD : ps.length ≤ (stream ps).length := by omega
  have hM : mass ps ≤ (stream ps).length := by omega
  have hs := scanCost_le query 0 ps
  have he := encodeIndices_length_le query 0 ps
  have hm := Nat.mul_le_mul hD
    (show 9*query+10*ps.length+215 ≤ 9*query+10*(stream ps).length+215 by omega)
  unfold budget
  nlinarith

theorem primitive_runs (query : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 5 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(1000*((stream ps).length+query+1)^2))
      (primitiveCfg program ((data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []).withPC
        (some program.entry)))
      (primitiveCfg program ((data rf (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))).withPC none)) := by
  obtain ⟨rf,n,hn,ht⟩ := program_runs query ps regs
  have hr : RunsIn program (1000*((stream ps).length+query+1)^2)
      ((data regs (unary query) (stream ps) [] [] [] [] [] [] [] [] []).withPC (some program.entry))
      ((data rf (unary query) (stream ps) [] [] [] [] [] [] []
        (unary (fiberIndices query 0 ps).length) (encodeIndices (fiberIndices query 0 ps))).withPC none) :=
    ⟨n,hn.trans (budget_polynomial query ps),ht⟩
  exact ⟨rf,primitive_execution program hr⟩

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
