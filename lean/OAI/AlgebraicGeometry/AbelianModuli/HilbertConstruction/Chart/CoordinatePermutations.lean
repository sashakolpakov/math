import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ChartBaseChange
import Mathlib.LinearAlgebra.Pi

/-! # Coordinate Permutations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.CoordinatePermutations

noncomputable section

/-! Permuting the ambient coordinates uniformly over every coefficient ring. -/

universe u v

/-- A permutation acts on functions by inverse reindexing. -/
def chartFunctionPermutation (R : Type u) [CommRing R] {ι : Type*} (τ : Equiv.Perm ι) :
    (ι → R) ≃ₗ[R] (ι → R) where
  toFun f i := f (τ.symm i)
  invFun f i := f (τ i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An ambient coordinate permutation acts on the two summands of a quotient chart. -/
def chartCoordinatePermutation (R : Type u) [CommRing R] {k l : ℕ}
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    ((Fin k → R) × (Fin l → R)) ≃ₗ[R] ((Fin k → R) × (Fin l → R)) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin l) R R).symm.trans
    ((chartFunctionPermutation R τ).trans (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin l) R R))

theorem chartCoordinatePermutation_fst (R : Type u) [CommRing R] {k l : ℕ}
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) (x : (Fin k → R) × (Fin l → R)) (i : Fin k) :
    (chartCoordinatePermutation R τ x).1 i = Sum.elim x.1 x.2 (τ.symm (Sum.inl i)) := rfl

theorem chartCoordinatePermutation_snd (R : Type u) [CommRing R] {k l : ℕ}
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) (x : (Fin k → R) × (Fin l → R)) (i : Fin l) :
    (chartCoordinatePermutation R τ x).2 i = Sum.elim x.1 x.2 (τ.symm (Sum.inr i)) := rfl

/-- Coordinate permutations commute with arbitrary scalar extension. -/
theorem chartCoordinatePermutation_naturality {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    (φ : R →+* B) {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))
    (x : (Fin k → R) × (Fin l → R)) :
    Matrix.ChartBaseChange.chartPairMap φ k l (chartCoordinatePermutation R τ x) =
      chartCoordinatePermutation B τ (Matrix.ChartBaseChange.chartPairMap φ k l x) := by
  apply Prod.ext
  · funext i
    change φ (Sum.elim x.1 x.2 (τ.symm (Sum.inl i))) =
      Sum.elim (fun j => φ (x.1 j)) (fun j => φ (x.2 j)) (τ.symm (Sum.inl i))
    cases τ.symm (Sum.inl i) <;> rfl
  · funext i
    change φ (Sum.elim x.1 x.2 (τ.symm (Sum.inr i))) =
      Sum.elim (fun j => φ (x.1 j)) (fun j => φ (x.2 j)) (τ.symm (Sum.inr i))
    cases τ.symm (Sum.inr i) <;> rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.CoordinatePermutations
