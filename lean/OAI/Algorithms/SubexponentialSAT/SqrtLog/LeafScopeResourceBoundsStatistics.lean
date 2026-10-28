import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramOrder
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramPositivity

namespace OAI.Algorithms

/-! Upper bounds for the actual measured statistics. The mask is the forward
reverse of the physical descending high-prefix stream. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram LeafStatisticsSemantics

abbrev forwardMask (scopes : List (List ℕ)) (cut n : ℕ) :=
  (HighIncidenceProgram.highPrefix scopes cut n).reverse

@[simp] theorem forwardMask_length (scopes : List (List ℕ)) (cut n : ℕ) :
    (forwardMask scopes cut n).length = n := by
  simp [forwardMask, HighIncidenceProgram.highPrefix_length]

theorem forwardMask_get (scopes : List (List ℕ)) (cut n : ℕ)
    (i : Fin (forwardMask scopes cut n).length) :
    (forwardMask scopes cut n).get i = decide (cut < degree scopes i.val) := by
  simp only [forwardMask, HighIncidenceProgram.Order.highPrefix_range,
    ← List.map_reverse, List.reverse_reverse, List.get_eq_getElem,
    List.getElem_map, List.getElem_range]

theorem measured_occurrence_le (scopes : List (List ℕ)) (cut n : ℕ) :
    (measured scopes (forwardMask scopes cut n)).occurrence ≤ max 1 cut := by
  rw [measured, occurrence_exact]
  apply Finset.sup_le
  intro v _
  rw [completed_degree]
  apply max_le_max_left
  have h := free_bit (forwardMask scopes cut n) v
  rw [forwardMask_get] at h
  simpa using h

theorem measured_arity_le (scopes : List (List ℕ)) (mask : List Bool) (A : ℕ)
    (ha : ∀ row ∈ scopes, row.length ≤ A) :
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered = 0 then 0 else 1) ≤ max A 1 := by
  apply max_le
  · apply le_trans _ (le_max_left A 1)
    apply (arity_le_iff mask scopes 0 A).mpr
    exact ⟨Nat.zero_le _, fun row hr => (List.length_filter_le _ _).trans (ha row hr)⟩
  · split_ifs <;> omega

theorem measured_uncovered_le (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).uncovered ≤ mask.length := by
  rw [measured, uncovered_exact]
  apply (Finset.card_le_univ _).trans
  simp

theorem measured_factors_le (scopes : List (List ℕ)) (mask : List Bool) :
    scopes.length + (measured scopes mask).uncovered ≤ scopes.length + mask.length :=
  Nat.add_le_add_left (measured_uncovered_le scopes mask) _

theorem cut_le_of_mass (scopes : List (List ℕ)) (nb tb : List Bool) (C : ℕ)
    (hn : 0 < BinaryArithmetic.toNat nb)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤ BinaryArithmetic.toNat nb * C) :
    HighIncidenceProgram.Prepare.cut scopes nb tb ≤ C * BinaryArithmetic.toNat tb := by
  apply (ceilDiv_le_iff_le_mul hn).mpr
  calc
    _ ≤ (BinaryArithmetic.toNat nb * C) * BinaryArithmetic.toNat tb := Nat.mul_le_mul_right _ hS
    _ = _ := by ring

theorem measured_occurrence_of_mass (scopes : List (List ℕ)) (nb tb : List Bool) (C : ℕ)
    (hn : 0 < BinaryArithmetic.toNat nb)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤ BinaryArithmetic.toNat nb * C) :
    (measured scopes (forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb)
      (BinaryArithmetic.toNat nb))).occurrence ≤ max 1 (C * BinaryArithmetic.toNat tb) :=
  (measured_occurrence_le _ _ _).trans (max_le_max_left 1 (cut_le_of_mass scopes nb tb C hn hS))

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
