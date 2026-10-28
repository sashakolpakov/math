/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatDecomposition.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FirstQuadrantTotalCoordinates

/-! # Degree Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Total.DegreeDecomposition.TotalComplex

noncomputable section

/-! Coordinates in every total degree of a first-quadrant double complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

/-- Every total degree is the finite sum of its bidegree components. -/
theorem totalUpNat_decomposition (n : ℕ) :
    ∑ i : Fin (n + 1), FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n ≫
      K.ιTotal (.up ℕ) i (n - i) n (by
        change (i : ℕ) + (n - i) = n
        omega) = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = n at h
  rw [Preadditive.comp_sum]
  let j : Fin (n + 1) := ⟨q, by omega⟩
  rw [Finset.sum_eq_single j]
  · have hp : p = n - q := by omega
    simp [j, hp]
  · intro i _ hij
    have hiq : q ≠ (i : ℕ) := by
      intro heq
      apply hij
      apply Fin.ext
      exact heq.symm
    simp [hiq]
  · simp

/-- A map into the total complex is determined by its finitely many bidegree coordinates. -/
theorem totalUpNat_hom_ext (n : ℕ) {A : C}
    {f g : A ⟶ (K.total (.up ℕ)).X n}
    (h : ∀ i : Fin (n + 1),
      f ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n = g ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n) : f = g := by
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = f ≫ ∑ i : Fin (n + 1), FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n ≫
        K.ιTotal (.up ℕ) i (n - i) n (by
          change (i : ℕ) + (n - i) = n
          omega) := by rw [totalUpNat_decomposition]
    _ = g ≫ ∑ i : Fin (n + 1), FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n ≫
        K.ιTotal (.up ℕ) i (n - i) n (by
          change (i : ℕ) + (n - i) = n
          omega) := by
      rw [Preadditive.comp_sum, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Category.assoc, ← Category.assoc, h i]
    _ = g := by rw [totalUpNat_decomposition, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Total.DegreeDecomposition.TotalComplex
