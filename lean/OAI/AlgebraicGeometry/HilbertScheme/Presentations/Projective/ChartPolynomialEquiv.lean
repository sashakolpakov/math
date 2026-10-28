import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra

/-! # Chart Polynomial Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartPolynomialEquiv

noncomputable section

/-! Each standard projective chart is explicitly a polynomial ring
in the remaining coordinates, over any coefficient ring. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra

universe u
variable (R : Type u) [CommRing R] {n : ℕ} (i : Fin (n + 1))

abbrev ProjectiveChartVariables := {j : Fin (n + 1) // j ≠ i}

def normalizedChartVariable (j : Fin (n + 1)) : MvPolynomial (ProjectiveChartVariables i) R :=
  if h : j = i then 1 else X ⟨j, h⟩

theorem normalizedChartVariable_self : normalizedChartVariable R i i = 1 := by
  simp [normalizedChartVariable]

def projectiveChartToPolynomial : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i →ₐ[R]
    MvPolynomial (ProjectiveChartVariables i) R :=
  AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra.projectiveChartEvaluationAlg (normalizedChartVariable R i) i (normalizedChartVariable_self R i)

def polynomialToProjectiveChart : MvPolynomial (ProjectiveChartVariables i) R →ₐ[R]
    AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i :=
  aeval (fun j => Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j.val))

theorem projectiveChartToPolynomial_coordinate (j : Fin (n + 1)) :
    projectiveChartToPolynomial R i (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j)) = normalizedChartVariable R i j :=
  AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate _ _ _ _

theorem polynomialToProjectiveChart_variable (j : ProjectiveChartVariables i) :
    polynomialToProjectiveChart R i (X j) = Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j.val) := aeval_X _ _

def projectiveChartPolynomialEquiv : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i ≃ₐ[R]
    MvPolynomial (ProjectiveChartVariables i) R :=
  AlgEquiv.ofAlgHom (projectiveChartToPolynomial R i) (polynomialToProjectiveChart R i)
    (by
      apply MvPolynomial.algHom_ext
      intro j
      simp only [AlgHom.comp_apply, polynomialToProjectiveChart_variable,
        projectiveChartToPolynomial_coordinate, normalizedChartVariable,
        dite_eq_right j.property, AlgHom.id_apply])
    (by
      apply AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra.projectiveChartAlgebra_ext i
      intro j
      simp only [AlgHom.comp_apply, projectiveChartToPolynomial_coordinate, AlgHom.id_apply]
      by_cases h : j = i
      · subst j
        rw [normalizedChartVariable_self, map_one, Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_self]
      · rw [normalizedChartVariable, dite_eq_right h, polynomialToProjectiveChart_variable])

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartPolynomialEquiv
