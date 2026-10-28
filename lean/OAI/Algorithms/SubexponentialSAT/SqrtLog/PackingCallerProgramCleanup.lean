import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

private theorem clear_cost_eq {S : ℕ} (ps : List (Fin S)) (hp : ps.Nodup) (a : State 16 S) :
    clearManyCost ps a=(ps.map (fun i=>2*(a.stacks i).length+3)).sum := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [clearManyCost,ih hp.tail]
    simp only [List.map_cons,List.sum_cons]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i≠p := by intro h; subst i; exact (List.nodup_cons.mp hp).1 hi
    simp [clearState,hne]

def clearLowBudget (d : Small) :=
  ((List.finRange 48).map (fun i=>2*(d.stacks i).length+3)).sum

theorem clearLow_cost (outside : Store) (d : Small) :
    clearManyCost lowClearPorts (framed outside d)=clearLowBudget d := by
  unfold lowClearPorts
  rw [clear_cost_eq _ (List.Nodup.map lowPorts.injective (List.nodup_finRange _))]
  simp [clearLowBudget,List.map_map,Function.comp_def]

theorem clearLow_run (outside : Store) (d : Small) :
    ∃ rf, Eval clearLow (clearLowBudget d)
      (framed outside d) (framed outside (⟨rf,fun _=>[]⟩ : Small)) := by
  simpa [clearLow_cost] using clearLow_eval outside d

theorem clearLowBudget_le (d : Small) (B : ℕ)
    (h : ∀ i,(d.stacks i).length ≤ B) : clearLowBudget d ≤ 48*(2*B+3) := by
  unfold clearLowBudget
  calc
    _ ≤ ((List.finRange 48).map (fun _=>2*B+3)).sum := by
      apply List.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3
    _ = _ := by
      have hsum (xs : List (Fin 48)) :
          (xs.map (fun _ => 2*B+3)).sum = xs.length*(2*B+3) := by
        induction xs with
        | nil => simp
        | cons x xs ih =>
            simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
            rw [Nat.add_mul,one_mul]
            exact Nat.add_comm _ _
      rw [hsum,List.length_finRange]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
