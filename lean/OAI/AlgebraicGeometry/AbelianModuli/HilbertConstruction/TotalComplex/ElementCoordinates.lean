import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryCoordinates
import Mathlib.Algebra.Category.Grp.Preadditive

/-! # Element Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.ElementCoordinates

noncomputable section

/-! Element coordinates for the genuine first-quadrant total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

private def homEvaluation {A B : AddCommGrpCat.{u}} (x : A) : (A ⟶ B) →+ B where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem hom_sum_apply {A B : AddCommGrpCat.{u}} {ι : Type*}
    (s : Finset ι) (f : ι → (A ⟶ B)) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  map_sum (homEvaluation x) f s

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- Every element of total degree `n` is the sum of its bidegree components. -/
theorem totalUpNat_element_decomposition (n : ℕ) (x : (K.total (.up ℕ)).X n) :
    ∑ i : Fin (n + 1),
      K.ιTotal (.up ℕ) i (n - i) n (by
        change (i : ℕ) + (n - i) = n
        omega) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n x) = x := by
  have h := congrArg (fun f => f x) (Total.DegreeDecomposition.TotalComplex.totalUpNat_decomposition K n)
  rw [hom_sum_apply] at h
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using h

/-- Vanishing of all total-degree coordinates is vanishing of the element. -/
theorem totalUpNat_eq_zero_of_coordinates (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (h : ∀ i : Fin (n + 1), FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n x = 0) : x = 0 := by
  rw [← totalUpNat_element_decomposition K n x]
  simp only [h, map_zero, Finset.sum_const_zero]

private theorem coordinate_inclusion_self (n : ℕ) (i : Fin (n + 1))
    (x : (K.X i).X (n - i)) :
    FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n
      (K.ιTotal (.up ℕ) i (n - i) n (by
        change (i : ℕ) + (n - i) = n
        omega) x) = x := by
  change (K.ιTotal (.up ℕ) i (n - i) n _ ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n) x = x
  simp

private theorem coordinate_inclusion_ne (n : ℕ) (i j : Fin (n + 1))
    (hij : i ≠ j) (x : (K.X i).X (n - i)) :
    FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K j (n - j) n
      (K.ιTotal (.up ℕ) i (n - i) n (by
        change (i : ℕ) + (n - i) = n
        omega) x) = 0 := by
  have h : (i : ℕ) ≠ (j : ℕ) := fun heq => hij (Fin.ext heq)
  change (K.ιTotal (.up ℕ) i (n - i) n _ ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K j (n - j) n) x = 0
  simp [h]

/-- The total degree is additively equivalent to its finite family of bidegree groups. -/
def totalCoordinateAddEquiv (n : ℕ) :
    (K.total (.up ℕ)).X n ≃+ ∀ i : Fin (n + 1), (K.X i).X (n - i) where
  toFun x i := FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n x
  invFun y := ∑ i : Fin (n + 1), K.ιTotal (.up ℕ) i (n - i) n (by
    change (i : ℕ) + (n - i) = n
    omega) (y i)
  left_inv x := totalUpNat_element_decomposition K n x
  right_inv y := by
    funext j
    change (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K j (n - j) n).hom
      (∑ i : Fin (n + 1), K.ιTotal (.up ℕ) i (n - i) n (by
        change (i : ℕ) + (n - i) = n
        omega) (y i)) = y j
    rw [map_sum, Finset.sum_eq_single j]
    · exact coordinate_inclusion_self K n j (y j)
    · intro i _ hij
      exact coordinate_inclusion_ne K n i j hij (y i)
    · simp
  map_add' x y := by
    funext i
    exact (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K i (n - i) n).hom.map_add x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.ElementCoordinates
