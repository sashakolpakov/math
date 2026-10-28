import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartMaps

/-! # Product Chart Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartEquivalence

noncomputable section

/-! Each Segre polynomial chart is the actual tensor product of the two projective chart rings. -/

open _root_.MvPolynomial

universe u

variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))

theorem segreProductChartInverse_row (a : Fin (n + 1)) :
    ProductChartMaps.segreProductChartInverse R i j
      (NormalizedCoordinates.segreRowCoordinate R (ULift.up i) (ULift.up j) (ULift.up a)) =
        Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X a)) := by
  classical
  by_cases ha : a = i
  · subst a
    simp [NormalizedCoordinates.segreRowCoordinate, HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_self, Algebra.TensorProduct.one_def]
  · simp [NormalizedCoordinates.segreRowCoordinate, ProductChartMaps.segreProductChartInverse, ha]

theorem segreProductChartInverse_column (b : Fin (m + 1)) :
    ProductChartMaps.segreProductChartInverse R i j
      (NormalizedCoordinates.segreColumnCoordinate R (ULift.up i) (ULift.up j) (ULift.up b)) =
        Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize j (X b)) := by
  classical
  by_cases hb : b = j
  · subst b
    simp [NormalizedCoordinates.segreColumnCoordinate, HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_self, Algebra.TensorProduct.one_def]
  · simp [NormalizedCoordinates.segreColumnCoordinate, ProductChartMaps.segreProductChartInverse, hb]

theorem segreProductChartForward_inverse :
    (ProductChartMaps.segreProductChartForward R i j).comp (ProductChartMaps.segreProductChartInverse R i j) =
      AlgHom.id R (ProductChartMaps.SegreFiniteChartRing R i j) := by
  apply MvPolynomial.algHom_ext
  intro k
  cases k with
  | inl a =>
    change ProductChartMaps.segreProductChartForward R i j
      (ProductChartMaps.segreProductChartInverse R i j (X (Sum.inl a))) = X (Sum.inl a)
    rw [ProductChartMaps.segreProductChartInverse, aeval_X]
    simp only [Sum.elim_inl]
    rw [ProductChartMaps.segreProductChartForward_left, ProductChartMaps.segreProductChartRow_coordinate]
    simp [NormalizedCoordinates.segreRowCoordinate, a.property]
  | inr b =>
    change ProductChartMaps.segreProductChartForward R i j
      (ProductChartMaps.segreProductChartInverse R i j (X (Sum.inr b))) = X (Sum.inr b)
    rw [ProductChartMaps.segreProductChartInverse, aeval_X]
    simp only [Sum.elim_inr]
    rw [ProductChartMaps.segreProductChartForward_right, ProductChartMaps.segreProductChartColumn_coordinate]
    simp [NormalizedCoordinates.segreColumnCoordinate, b.property]

theorem segreProductChartInverse_forward :
    (ProductChartMaps.segreProductChartInverse R i j).comp (ProductChartMaps.segreProductChartForward R i j) =
      AlgHom.id R (ProductChartMaps.ProjectiveProductChartRing R i j) := by
  apply Algebra.TensorProduct.ext
  · apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext (R := R) (A := ProductChartMaps.ProjectiveProductChartRing R i j) i
    intro a
    change ProductChartMaps.segreProductChartInverse R i j
      (ProductChartMaps.segreProductChartForward R i j (Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X a)))) = _
    rw [ProductChartMaps.segreProductChartForward_left, ProductChartMaps.segreProductChartRow_coordinate, segreProductChartInverse_row]
    rfl
  · apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext (R := R) (A := ProductChartMaps.ProjectiveProductChartRing R i j) j
    intro b
    change ProductChartMaps.segreProductChartInverse R i j
      (ProductChartMaps.segreProductChartForward R i j (Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize j (X b)))) = _
    rw [ProductChartMaps.segreProductChartForward_right, ProductChartMaps.segreProductChartColumn_coordinate, segreProductChartInverse_column]
    rfl

def segreProductChartEquiv : ProductChartMaps.ProjectiveProductChartRing R i j ≃ₐ[R] ProductChartMaps.SegreFiniteChartRing R i j :=
  AlgEquiv.ofAlgHom (ProductChartMaps.segreProductChartForward R i j) (ProductChartMaps.segreProductChartInverse R i j)
    (segreProductChartForward_inverse R i j) (segreProductChartInverse_forward R i j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartEquivalence
