import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheAlgebra
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-! Numeric traversal and truncation identities for the actual Lagrange fold. -/

noncomputable section

namespace SubexponentialSAT.SubexpLagrangeCacheSemantics

open Polynomial SubexpLagrangeCacheAlgebra

section OrderedLabels

variable {A : Type*} [CommMonoid A]

theorem orderedProduct_range {p : ℕ} (f : ℕ → A) (i : Fin p) :
    orderedProduct f i.val (List.range p) =
      orderedProduct (fun j : Fin p => f j.val) i (List.finRange p) := by
  have hrange : (List.finRange p).map Fin.val = List.range p := by
    apply List.ext_getElem
    · simp
    · intro j hmap hrange
      rw [List.getElem_map, List.getElem_finRange, List.getElem_range]
      rfl
  rw [← hrange]
  simp only [orderedProduct, List.filter_map, List.map_map, Function.comp_def,
    Fin.val_ne_iff]

theorem orderedProduct_range_succ (f : ℕ → A) (i j n : ℕ) :
    orderedProduct f i (List.range' j (n + 1)) =
      (if i = j then 1 else f j) * orderedProduct f i (List.range' (j + 1) n) := by
  by_cases h : i = j
  · subst j
    simp [orderedProduct, List.range'_succ]
  · simp [orderedProduct, List.range'_succ, h, Ne.symm h]

end OrderedLabels

theorem trunc_numerator {R : Type*} [CommRing R] {p : ℕ}
    (hp : 0 < p) (v : Fin p → R) (i : Fin p) :
    Truncation.trunc p (numerator v i) = numerator v i := by
  ext j
  rw [Truncation.coeff_trunc]
  split_ifs with hj
  · rfl
  · exact (numerator_coeff_eq_zero hp v i (Nat.le_of_not_gt hj)).symm

end SubexponentialSAT.SubexpLagrangeCacheSemantics

end
end OAI.Algorithms
