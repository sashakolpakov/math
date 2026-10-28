import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMatrices

/-! # Overlap Determinants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapDeterminants

noncomputable section

/-! Universal determinant equations for overlaps of Grassmannian affine charts. -/

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] {k l : ℕ}

/-- A coordinate-permuted first block is invertible exactly when its overlap determinant is a unit. -/
theorem quotientChart_overlap_iff (c : Quotient.Charts.QuotientChart A (Fin k → A) (Fin l → A))
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    Function.Bijective (c.firstBlock (CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap) ↔
      IsUnit (OverlapMatrices.chartOverlapMatrix (LinearMap.toMatrix' c.coordinates) τ).det := by
  have he : (LinearMap.toMatrix' c.coordinates).mulVecLin = c.coordinates :=
    LinearMap.toMatrix'.symm_apply_apply _
  have hp : OverlapMatrices.chartMatrixProjection (LinearMap.toMatrix' c.coordinates) = c.projection :=
    congrArg (fun L => LinearMap.id.coprod L) he
  have hm : (OverlapMatrices.chartOverlapMatrix (LinearMap.toMatrix' c.coordinates) τ).mulVecLin =
      c.firstBlock (CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap := by
    exact (LinearMap.toMatrix'.symm_apply_apply _).trans
      (congrArg (fun q => q.comp ((CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap.comp
        (LinearMap.inl A (Fin k → A) (Fin l → A)))) hp)
  have hb : Function.Bijective (OverlapMatrices.chartOverlapMatrix (LinearMap.toMatrix' c.coordinates) τ).mulVec ↔
      Function.Bijective (c.firstBlock (CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap) :=
    Iff.of_eq (congrArg (fun q : (Fin k → A) →ₗ[A] (Fin k → A) => Function.Bijective q) hm)
  exact hb.symm.trans (Grassmann.FrameDeterminants.matrix_bijective_iff_isUnit_det _)

/-- The determinant polynomial cutting out the overlap with the chart selected by `τ`. -/
def chartOverlapPolynomial (R : Type u) [CommRing R] {k l : ℕ}
    (τ : Equiv.Perm (Fin k ⊕ Fin l)) : MvPolynomial (Fin k × Fin l) R :=
  (OverlapMatrices.chartOverlapMatrix (fun i j => MvPolynomial.X (i, j)) τ).det

/-- Evaluation of the universal overlap equation is the determinant of the alternate frame. -/
theorem chartOverlapPolynomial_eval [Algebra R A]
    (φ : MvPolynomial (Fin k × Fin l) R →ₐ[R] A) (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    φ (chartOverlapPolynomial R τ) =
      (OverlapMatrices.chartOverlapMatrix (Grassmann.PolynomialCoordinates.grassmannChartMatrixEquiv (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv φ)) τ).det := by
  have hm : Matrix.map (fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin k × Fin l) R))
      φ.toRingHom = Grassmann.PolynomialCoordinates.grassmannChartMatrixEquiv (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv φ) := by
    ext i j
    exact (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv_matrix φ i j).symm
  exact (OverlapMatrices.chartOverlapDet_naturality φ.toRingHom (fun i j => MvPolynomial.X (i, j)) τ).trans
    (congrArg (fun M => (OverlapMatrices.chartOverlapMatrix M τ).det) hm)

/-- The universal determinant equation detects precisely the chart overlap on every algebra. -/
theorem chartOverlapPolynomial_isUnit_iff [Algebra R A]
    (φ : MvPolynomial (Fin k × Fin l) R →ₐ[R] A) (τ : Equiv.Perm (Fin k ⊕ Fin l)) :
    IsUnit (φ (chartOverlapPolynomial R τ)) ↔
      Function.Bijective ((Grassmann.Charts.grassmannQuotientChartEquiv (Grassmann.PolynomialCoordinates.grassmannChartPolynomialEquiv φ)).firstBlock
        (CoordinatePermutations.chartCoordinatePermutation A τ).toLinearMap) := by
  rw [chartOverlapPolynomial_eval]
  exact (quotientChart_overlap_iff _ τ).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapDeterminants
