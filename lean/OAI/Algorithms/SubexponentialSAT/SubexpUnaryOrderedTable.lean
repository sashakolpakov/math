import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLEFactorSystem
import OAI.Algorithms.SubexponentialSAT.SubexpLeafTables
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFactorTable

namespace OAI.Algorithms

/-! The raw descending unary table is the ordered LE factor table.
The singleton scope has no hidden coordinate permutation. -/

namespace SubexponentialSAT.SubexpUnaryOrderedTable

open SubexpDigitGrid SubexpTableInterpolation

private theorem first_digit (p : ℕ) (rank : Fin (p ^ 1)) :
    ((rankEquiv p 1 rank).get 0).val = rank.val := by
  change rank.val % p = rank.val
  exact Nat.mod_eq_of_lt (by simpa only [pow_one] using rank.isLt)

private theorem bool_self (b : Bool) : (if b = true then true else false) = b := by
  cases b <;> rfl

variable {n D p : ℕ} [Fact p.Prime] {b : Fin D → ℕ}
variable (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
variable (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF (Fin n))

/-- Any equivalence of the singleton scope has the same sole coordinate.
In particular this applies to `scopeOfList` of the physically emitted `[j]`. -/
theorem table_eq_orderedRows (j : Fin D)
    (scope : Fin 1 ≃
      {v // v ∈ (SubexpLEFactorSystem.system positions capacity F).scope (.inl j)}) :
    SubexpUnaryFactorTable.table (b j) p =
      (SubexpLeafTables.orderedRows (SubexpLEFactorSystem.system positions capacity F)
        (.inl j) scope false true).map Row.value := by
  have htable (a : List.Vector (Fin p) 1) :
      (SubexpLEFactorSystem.system positions capacity F).table (.inl j)
        (fun v => ZMod.finEquiv p (a.get (scope.symm v))) =
        decide ((a.get 0).val < 2 ^ b j) := by
    have hx : (fun v => ZMod.finEquiv p (a.get (scope.symm v))) =
        (fun _ => ZMod.finEquiv p (a.get 0)) := by
      funext v
      rw [show scope.symm v = 0 from Subsingleton.elim _ _]
    rw [hx]
    apply Bool.eq_iff_iff.mpr
    simpa only [Factor.evalFactor, decide_eq_true_eq, BooleanPacking.finEquiv_val] using
      SubexpLEFactorSystem.unary_iff positions capacity F
        (fun _ => ZMod.finEquiv p (a.get 0)) j
  symm
  simp only [SubexpLeafTables.orderedRows, rows, List.map_map, Function.comp_def]
  simp_rw [htable, bool_self]
  simp only [descending, ascending, List.map_reverse, List.map_map, Function.comp_def,
    first_digit]
  calc
    _ = (((List.finRange (p ^ 1)).map Fin.val).map
        (fun rank => decide (rank < 2 ^ b j))).reverse := by
      rw [List.map_map]
      rfl
    _ = ((List.range p).map (fun rank => decide (rank < 2 ^ b j))).reverse := by
      rw [List.map_coe_finRange, pow_one]
    _ = SubexpUnaryFactorTable.table (b j) p := by
      simp only [SubexpUnaryFactorTable.table, SubexpUnaryRowEnumeration.rows,
        SubexpUnaryRowProgram.answer,
        List.range'_eq_map_range, Nat.zero_add, List.map_reverse,
        List.map_map, Function.comp_def]

end SubexponentialSAT.SubexpUnaryOrderedTable

end OAI.Algorithms
