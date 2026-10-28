import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredMatrixUnitProjection

/-! # Upper Unitriangular Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularGroup.Construction

noncomputable section

/-! The standard upper unitriangular group preserves every decreasing
weight filtration; its weight-block projection is unitriangular. -/

open scoped Classical

def upperUnitriangularMatrixGroup (n : ℕ) : Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ where
  carrier := {g | UpperUnitriangularMatrices.Construction.IsUpperUnitriangular g.val}
  one_mem' := ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' {g} hg := hg.unit_inv g

theorem upperUnitriangularMatrixGroup_isClosed (n : ℕ) :
    IsClosed (upperUnitriangularMatrixGroup n : Set (Matrix (Fin n) (Fin n) ℝ)ˣ) :=
  (UpperUnitriangularMatrices.Construction.isClosed_upper_unitriangular n).preimage Units.continuous_val

theorem upper_triangular_ordered_weight_filtered {n : ℕ}
    (w : Fin n → ℝ) (hw : Antitone w) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsUpperTriangular) : Matrix.BlockTriangular (α := OrderDual ℝ) M w := by
  intro i j hij
  have hji : j < i := by
    by_contra hn
    exact (not_lt_of_ge (hw (le_of_not_gt hn))) hij
  exact hM hji

def upperUnitriangularFilteredHom {n : ℕ} (w : Fin n → ℝ) (hw : Antitone w) :
    upperUnitriangularMatrixGroup n →* FilteredMatrixUnitProjection.Construction.weightFilteredMatrixUnits w :=
  Subgroup.inclusion (by
    intro g hg
    exact ⟨upper_triangular_ordered_weight_filtered w hw g.val hg.1,
      upper_triangular_ordered_weight_filtered w hw (g⁻¹).val (hg.unit_inv g).1⟩)

theorem weightBlockProjection_upper_unitriangular {n : ℕ} (w : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular M) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (Weight.BlockProjection.Construction.weightBlockProjection w M) := by
  constructor
  · intro i j hij
    rw [Weight.BlockProjection.Construction.weightBlockProjection_apply, hM.1 hij]
    split_ifs <;> rfl
  · intro i
    rw [Weight.BlockProjection.Construction.weightBlockProjection_apply, ite_eq_left rfl, hM.2 i]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularGroup.Construction
