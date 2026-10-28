import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperPivotElimination
import OAI.NumberTheory.ArithmeticGroups.Lattices.IsolatedPivotMatrices
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Upper Monomial Elimination -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMonomialElimination.Construction

noncomputable section

/-! Upper unitriangular operations reduce every invertible real
matrix to a matrix supported on a permutation. -/

open scoped Classical

def isolatedPivotPermutation {n : ℕ} (r c : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' c).symm)

@[simp] theorem isolatedPivotPermutation_pivot {n : ℕ}
    (r c : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) : isolatedPivotPermutation r c σ r = c := by
  simp [isolatedPivotPermutation]

@[simp] theorem isolatedPivotPermutation_minor {n : ℕ}
    (r c : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    isolatedPivotPermutation r c σ (r.succAbove i) = c.succAbove (σ i) := by
  simp [isolatedPivotPermutation]

theorem isolatedPivotMatrix_permutation_support {n : ℕ}
    (r c : Fin (n + 1)) (M : Matrix (Fin n) (Fin n) ℝ) (a : ℝ)
    (σ : Equiv.Perm (Fin n)) (hM : ∀ i j, j ≠ σ i → M i j = 0)
    (i j : Fin (n + 1)) (hij : j ≠ isolatedPivotPermutation r c σ i) :
    IsolatedPivotMatrices.Construction.isolatedPivotMatrix r c M a i j = 0 := by
  cases i using Fin.succAboveCases r with
  | x =>
    cases j using Fin.succAboveCases c with
    | x => exact (hij (isolatedPivotPermutation_pivot r c σ).symm).elim
    | p j => simp
  | p i =>
    cases j using Fin.succAboveCases c with
    | x => simp
    | p j =>
      rw [IsolatedPivotMatrices.Construction.isolatedPivotMatrix_minor]
      apply hM i j
      intro he
      apply hij
      simp [he]

theorem exists_upper_monomial_elimination (n : ℕ)
    (M : (Matrix (Fin n) (Fin n) ℝ)ˣ) :
    ∃ U V : Matrix (Fin n) (Fin n) ℝ, ∃ σ : Equiv.Perm (Fin n),
      UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U ∧ UpperUnitriangularMatrices.Construction.IsUpperUnitriangular V ∧
      ∀ i j, j ≠ σ i → (U * M.val * V) i j = 0 := by
  induction n with
  | zero =>
    exact ⟨1, 1, Equiv.refl _, ⟨Matrix.blockTriangular_one, fun i => Fin.elim0 i⟩,
      ⟨Matrix.blockTriangular_one, fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨p, U, V, hU, hV, _, hrow, hcol⟩ := UpperPivotElimination.Construction.exists_upper_pivot_elimination M
    let R := U * M.val * V
    let A := R.submatrix (Fin.last n).succAbove p.succAbove
    let a := R (Fin.last n) p
    have hR : R = IsolatedPivotMatrices.Construction.isolatedPivotMatrix (Fin.last n) p A a :=
      IsolatedPivotMatrices.Construction.eq_isolatedPivotMatrix (Fin.last n) p R hrow hcol
    have hRu : IsUnit R := (hU.isUnit.mul M.isUnit).mul hV.isUnit
    have hA : IsUnit A := IsolatedPivotMatrices.Construction.isolatedPivotMatrix_minor_isUnit _ _ A a (hR ▸ hRu)
    obtain ⟨U₀, V₀, σ, hU₀, hV₀, hs⟩ := ih hA.unit
    have hs' : ∀ i j, j ≠ σ i → (U₀ * A * V₀) i j = 0 := by
      simpa only [hA.unit_spec] using hs
    let U₁ := IsolatedPivotMatrices.Construction.isolatedPivotMatrix (Fin.last n) (Fin.last n) U₀ 1
    let V₁ := IsolatedPivotMatrices.Construction.isolatedPivotMatrix p p V₀ 1
    have he : (U₁ * U) * M.val * (V * V₁) =
        IsolatedPivotMatrices.Construction.isolatedPivotMatrix (Fin.last n) p (U₀ * A * V₀) a := by
      calc
        (U₁ * U) * M.val * (V * V₁) = U₁ * R * V₁ := by simp only [R, mul_assoc]
        _ = IsolatedPivotMatrices.Construction.isolatedPivotMatrix (Fin.last n) p (U₀ * A * V₀) a := by
          rw [hR]
          change IsolatedPivotMatrices.Construction.isolatedPivotMatrix _ _ _ _ * IsolatedPivotMatrices.Construction.isolatedPivotMatrix _ _ _ _ *
            IsolatedPivotMatrices.Construction.isolatedPivotMatrix _ _ _ _ = _
          rw [IsolatedPivotMatrices.Construction.isolatedPivotMatrix_mul, IsolatedPivotMatrices.Construction.isolatedPivotMatrix_mul, one_mul, mul_one]
    refine ⟨U₁ * U, V * V₁, isolatedPivotPermutation (Fin.last n) p σ,
      (IsolatedPivotMatrices.Construction.isolatedPivotMatrix_unitriangular _ _ hU₀).mul hU,
      hV.mul (IsolatedPivotMatrices.Construction.isolatedPivotMatrix_unitriangular _ _ hV₀), ?_⟩
    intro i j hij
    rw [he]
    exact isolatedPivotMatrix_permutation_support _ _ _ _ σ hs' i j hij

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMonomialElimination.Construction
