import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Raising Nilpotence -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingNilpotence.Construction

noncomputable section

/-! An operator whose matrix strictly raises a finite family of real
weights is nilpotent. Block triangularity and Cayley--Hamilton give the proof. -/

open scoped Classical
open _root_.Matrix _root_.Polynomial

theorem strictly_weight_raising_matrix_isNilpotent
    {R ι α : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder α]
    (M : Matrix ι ι R) (w : ι → α) (hM : ∀ i j, w i ≤ w j → M i j = 0) : IsNilpotent M := by
  let b : ι → OrderDual α := w
  have ht : M.BlockTriangular b := fun i j hij => hM i j (le_of_lt hij)
  have hb (r : OrderDual α) : M.toSquareBlock b r = 0 := by
    ext i j
    apply hM
    exact le_of_eq (i.property.trans j.property.symm)
  have hchar : ∃ d : ℕ, M.charpoly = X ^ d := by
    rw [ht.charpoly]
    simp only [hb, Matrix.charpoly_zero, Finset.prod_pow_eq_pow_sum]
    exact ⟨_, rfl⟩
  obtain ⟨d, hd⟩ := hchar
  refine ⟨d, ?_⟩
  have he := M.aeval_self_charpoly
  rwa [hd, map_pow, aeval_X] at he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingNilpotence.Construction
