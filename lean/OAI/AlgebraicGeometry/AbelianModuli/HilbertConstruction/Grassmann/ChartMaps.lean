import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ChartBaseChange

/-! # Chart Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann

noncomputable section

/-! Functorial scalar extension in the Grassmannian quotient charts. -/

universe u v w

variable {R : Type u} {B : Type v} {C : Type w} [CommRing R] [CommRing B] [CommRing C]
  {k l : ℕ}

/-- Express the defining submodule by the matrix of the chart point. -/
theorem Charts.GrassmannChart.kernel_eq_matrix (c : Charts.GrassmannChart R (Fin l → R) k) :
    c.val.toSubmodule = (LinearMap.id.coprod (PolynomialCoordinates.grassmannChartMatrixEquiv c).mulVecLin).ker := by
  let q := Charts.grassmannQuotientChartEquiv c
  have he : (PolynomialCoordinates.grassmannChartMatrixEquiv c).mulVecLin = q.coordinates :=
    LinearMap.toMatrix'.symm_apply_apply q.coordinates
  exact q.kernel_eq.trans (congrArg (fun L => (LinearMap.id.coprod L).ker) he.symm)

/-- Extend a chart point by applying the scalar homomorphism to its matrix coefficients. -/
def Charts.GrassmannChart.map (φ : R →+* B) (c : Charts.GrassmannChart R (Fin l → R) k) :
    Charts.GrassmannChart B (Fin l → B) k :=
  PolynomialCoordinates.grassmannChartMatrixEquiv.symm ((PolynomialCoordinates.grassmannChartMatrixEquiv c).map φ)

theorem Charts.GrassmannChart.map_matrix (φ : R →+* B) (c : Charts.GrassmannChart R (Fin l → R) k) :
    PolynomialCoordinates.grassmannChartMatrixEquiv (Charts.GrassmannChart.map φ c) = (PolynomialCoordinates.grassmannChartMatrixEquiv c).map φ :=
  PolynomialCoordinates.grassmannChartMatrixEquiv.apply_symm_apply _

/-- The coordinate construction extends the actual defining submodule by the new scalars. -/
theorem Charts.GrassmannChart.map_kernel (φ : R →+* B) (c : Charts.GrassmannChart R (Fin l → R) k) :
    (Charts.GrassmannChart.map φ c).val.toSubmodule = Submodule.span B
      (Matrix.ChartBaseChange.chartPairMap φ k l '' (c.val.toSubmodule : Set ((Fin k → R) × (Fin l → R)))) := by
  rw [Charts.GrassmannChart.kernel_eq_matrix, Charts.GrassmannChart.map_matrix, c.kernel_eq_matrix]
  exact (Matrix.ChartBaseChange.matrixChart_kernel_baseChange φ (PolynomialCoordinates.grassmannChartMatrixEquiv c)).symm

theorem Charts.GrassmannChart.map_id (c : Charts.GrassmannChart R (Fin l → R) k) : Charts.GrassmannChart.map (RingHom.id R) c = c := by
  apply PolynomialCoordinates.grassmannChartMatrixEquiv.injective
  rw [Charts.GrassmannChart.map_matrix]
  rfl

theorem Charts.GrassmannChart.map_comp (φ : R →+* B) (ψ : B →+* C) (c : Charts.GrassmannChart R (Fin l → R) k) :
    Charts.GrassmannChart.map (ψ.comp φ) c = Charts.GrassmannChart.map ψ (Charts.GrassmannChart.map φ c) := by
  apply PolynomialCoordinates.grassmannChartMatrixEquiv.injective
  rw [Charts.GrassmannChart.map_matrix, Charts.GrassmannChart.map_matrix, Charts.GrassmannChart.map_matrix]
  rfl

/-- Polynomial coordinates commute with scalar extension of the actual quotient. -/
theorem Charts.GrassmannChart.polynomialEquiv_naturality [Algebra R B] [Algebra R C] (ψ : B →ₐ[R] C)
    (φ : MvPolynomial (Fin k × Fin l) R →ₐ[R] B) :
    PolynomialCoordinates.grassmannChartPolynomialEquiv (ψ.comp φ) = Charts.GrassmannChart.map ψ.toRingHom (PolynomialCoordinates.grassmannChartPolynomialEquiv φ) := by
  apply PolynomialCoordinates.grassmannChartMatrixEquiv.injective
  ext i j
  rw [PolynomialCoordinates.grassmannChartPolynomialEquiv_matrix, Charts.GrassmannChart.map_matrix]
  change ψ (φ (MvPolynomial.X (i, j))) =
    ψ (PolynomialCoordinates.grassmannChartMatrixEquiv (PolynomialCoordinates.grassmannChartPolynomialEquiv φ) i j)
  rw [PolynomialCoordinates.grassmannChartPolynomialEquiv_matrix]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann
