/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatDecomposition.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Total.DegreeDecomposition

/-! # Boundary Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryCoordinates

noncomputable section

/-! Boundary-coordinate formulas in arbitrary total degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
    (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

/-- At the zeroth vertical coordinate, the total differential is the row differential. -/
theorem total_d_π_zero (n : ℕ) :
    (K.total (.up ℕ)).d n (n + 1) ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K 0 (n + 1) (n + 1) =
      FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K 0 n n ≫ (K.X 0).d n (n + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = n at h
  subst n
  rw [FirstQuadrantTotalCoordinates.TotalComplex.ιTotal_d_upNat_assoc K]
  cases q with
  | zero => simp [HomologicalComplex₂.XXIsoOfEq]
  | succ q => simp

/-- At the zeroth horizontal coordinate, the total differential is the column differential. -/
theorem total_d_π_zero_right (n : ℕ) :
    (K.total (.up ℕ)).d n (n + 1) ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (n + 1) 0 (n + 1) =
      FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n ≫ (K.d n (n + 1)).f 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = n at h
  subst n
  rw [FirstQuadrantTotalCoordinates.TotalComplex.ιTotal_d_upNat_assoc K]
  cases p with
  | zero => simp
  | succ p => simp

/-- The total differential formula with an explicitly named total degree. -/
@[reassoc]
theorem ιTotal_d_of_sum (q p n : ℕ) (h : q + p = n) :
    K.ιTotal (.up ℕ) q p n h ≫ (K.total (.up ℕ)).d n (n + 1) =
      (K.d q (q + 1)).f p ≫
          K.ιTotal (.up ℕ) (q + 1) p (n + 1) (by
            change q + 1 + p = n + 1
            omega) +
        ((-1 : ℤˣ) ^ q) • ((K.X q).d p (p + 1) ≫
          K.ιTotal (.up ℕ) q (p + 1) (n + 1) (by
            change q + (p + 1) = n + 1
            omega)) := by
  subst n
  exact FirstQuadrantTotalCoordinates.TotalComplex.ιTotal_d_upNat K q p

/-- Every interior output coordinate receives exactly its two adjacent input coordinates. -/
theorem total_d_π_interior (q p : ℕ) :
    (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1) ≫
        FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (q + 1) (p + 1) (q + p + 1 + 1) =
      FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q (p + 1) (q + p + 1) ≫ (K.d q (q + 1)).f (p + 1) +
        ((-1 : ℤˣ) ^ (q + 1)) •
          (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (q + 1) p (q + p + 1) ≫ (K.X (q + 1)).d p (p + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = q + p + 1 at h
  rw [ιTotal_d_of_sum_assoc]
  by_cases ha : a = q
  · have hb : b = p + 1 := by omega
    subst a b
    simp [HomologicalComplex₂.XXIsoOfEq]
  · by_cases ha' : a = q + 1
    · have hb : b = p := by omega
      subst a b
      simp [HomologicalComplex₂.XXIsoOfEq, Nat.add_assoc]
    · simp [ha, ha']

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.BoundaryCoordinates
