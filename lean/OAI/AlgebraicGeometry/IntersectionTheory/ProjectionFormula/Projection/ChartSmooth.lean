import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartPolynomialExtension
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Chart Smooth -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartSmooth

noncomputable section

/-! The native ring map on each coordinate-projection chart is
standard smooth of the expected relative dimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem polynomial (R ι : Type) [CommRing R] [Nontrivial R] [Fintype ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card ι) R (MvPolynomial ι R) := by
  let : Algebra.IsStandardSmooth R (MvPolynomial ι R) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential
      (KaehlerDifferential.mvPolynomialBasis R ι) (by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R ι i).symm⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  simpa using (KaehlerDifferential.mvPolynomialBasis R ι).mk_eq_rank.symm

theorem chart {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j) (i : Fin (m + 1)) :
    RingHom.IsStandardSmoothOfRelativeDimension (n - m) (HomogeneousChartRenaming.chartMap j i) := by
  let : IsDomain (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) := Function.Injective.isDomain
    (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i) (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRingEquiv m i).injective
  let : Algebra (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i)) :=
    (HomogeneousChartRenaming.chartMap j i).toAlgebra
  let := Fintype.ofFinite (ChartPolynomialExtension.extra j hj i)
  have hc : Fintype.card (ChartPolynomialExtension.extra j hj i) = n - m := by
    have he := ChartPolynomialExtension.card_extra j hj i
    rw [Nat.card_eq_fintype_card] at he
    omega
  let : Algebra.IsStandardSmoothOfRelativeDimension (n - m) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i)
      (MvPolynomial (ChartPolynomialExtension.extra j hj i) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i)) := by
    rw [← hc]
    exact polynomial (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i) (ChartPolynomialExtension.extra j hj i)
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n - m)
    (ChartPolynomialExtension.algebraEquiv j hj i).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartSmooth
