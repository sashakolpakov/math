import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageServices
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockwiseEnumeration

namespace OAI.Algorithms

/-!
# The actual coefficient order of the matrix-image program

The program prepends its matrix images, so its coefficient order is the
reverse of the tuple generator's order. These finite equivalences use that
literal list and its `get`/`idxOf` inverse. They supply the index order for
layout enumeration without changing any emitted bank bytes.
-/

namespace SubexponentialSAT.Subexp.MatrixCoefficientOrder

open ConstructivePacking MatrixImageEnumeration

variable (p : ℕ) [Fact p.Prime]

def enumeration (d : ℕ) : FiniteEnumeration (Fin d → ZMod p) where
  values := (coefficients p d).reverse
  nodup := List.nodup_reverse.mpr (coefficients_nodup p d)
  complete x := List.mem_reverse.mpr (mem_coefficients p d x)

@[simp] theorem enumeration_length (d : ℕ) : (enumeration p d).values.length = p ^ d := by
  simp only [enumeration, List.length_reverse, coefficients_length]

/-- Actual output indices, including the physical prepend reversal. -/
def coefficientsEquiv (d : ℕ) :
    Fin (enumeration p d).values.length ≃ (Fin d → ZMod p) :=
  (enumeration p d).equivFin

theorem ofFn_coefficientsEquiv (d : ℕ) :
    List.ofFn (coefficientsEquiv p d) = (coefficients p d).reverse :=
  List.ofFn_get _

theorem ofFn_map {A : Type*} (d : ℕ) (f : (Fin d → ZMod p) → A) :
    List.ofFn (fun i => f (coefficientsEquiv p d i)) =
      (coefficients p d).reverse.map f := by
  rw [← Function.comp_def, ← List.map_ofFn, ofFn_coefficientsEquiv]

/-- Exact equality with the output list used by the physical matrix-image
driver, for every concrete matrix. -/
theorem bankRecords_eq {D d : ℕ} (M : Fin D → Fin d → ZMod p) :
    List.ofFn (fun i => bank p M (coefficientsEquiv p d i)) = bankRecords p M := by
  rw [ofFn_map, List.map_reverse]
  rfl

/-- Read those same numeric coefficients at an explicit semantic column
index. The supplied column enumeration is the assembler's actual order. -/
def order {C : Type*} {d : ℕ} (columns : Fin d ≃ C) :
    Fin (enumeration p d).values.length ≃ (C → ZMod p) :=
  (coefficientsEquiv p d).trans (BlockwiseEnumeration.reindexFunction columns.symm)

@[simp] theorem order_apply {C : Type*} {d : ℕ} (columns : Fin d ≃ C)
    (i : Fin (enumeration p d).values.length) (c : C) :
    order p columns i c = coefficientsEquiv p d i (columns.symm c) := rfl

end SubexponentialSAT.Subexp.MatrixCoefficientOrder

end OAI.Algorithms
