import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramOrder

namespace OAI.Algorithms

/-! Exact original-variable meaning of the physical high-value vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem zeroMerge_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    zeroMerge (xs.map p) ((xs.filter p).map x) =
      xs.map (fun v => if p v then x v else false) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [zeroMerge, merge, hp, ih]

theorem high_vector (scopes : List (List ℕ)) (cut n : ℕ)
    (a : HighIncidence.high (suppliedScope n scopes) cut → Bool) :
    (zeroMerge (highPrefix scopes cut n)
      (List.ofFn (fun i => a (Order.highOrder (HighIncidence.high (suppliedScope n scopes) cut) i)))).reverse =
      List.ofFn (HighIncidence.glue (HighIncidence.high (suppliedScope n scopes) cut) a (fun _ => false)) := by
  let H := HighIncidence.high (suppliedScope n scopes) cut
  let x := HighIncidence.glue H a (fun _ => false)
  have hhigh : List.ofFn (fun i => a (Order.highOrder H i)) = (Order.highCoordinates H).map x := by
    rw [← Order.highOrder_stream]
    congr 1
    funext i
    simp [x, HighIncidence.glue, (Order.highOrder H i).property]
  change (zeroMerge _ (List.ofFn (fun i => a (Order.highOrder H i)))).reverse = List.ofFn x
  rw [hhigh, Order.physical_mask]
  change (zeroMerge ((Order.coordinates n).map (fun v => decide (v ∈ H)))
    (((Order.coordinates n).filter (fun v => decide (v ∈ H))).map x)).reverse = _
  rw [zeroMerge_map]
  have hx : (fun v => if decide (v ∈ H) then x v else false) = x := by
    funext v
    by_cases hv : v ∈ H <;> simp [hv, x, HighIncidence.glue]
  rw [hx, Order.coordinates_stream, List.reverse_reverse]

theorem high_vector_runsIn (regs : Fin 4 → Bool) (scopes : List (List ℕ)) (cut n : ℕ)
    (a : HighIncidence.high (suppliedScope n scopes) cut → Bool) :
    ∃ rf, RunsIn program (5 * n + 3)
      ((state regs (highPrefix scopes cut n)
        (List.ofFn (fun i => a (Order.highOrder (HighIncidence.high (suppliedScope n scopes) cut) i)))
        [] []).withPC (some program.entry))
      ((state rf [] [] []
        (List.ofFn (HighIncidence.glue (HighIncidence.high (suppliedScope n scopes) cut) a (fun _ => false)))).withPC none) := by
  obtain ⟨rf, hr⟩ := zero_program_runsIn regs (highPrefix scopes cut n)
    (List.ofFn (fun i => a (Order.highOrder (HighIncidence.high (suppliedScope n scopes) cut) i))) [] (by
      simp only [List.length_ofFn]
      exact (highPrefix_count_eq_card scopes cut n).symm)
  refine ⟨rf, ?_⟩
  simpa only [highPrefix_length, List.append_nil, high_vector] using hr

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
