import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Dehomogenization

/-! # Homogeneous Chart Renaming -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming

noncomputable section

/-! The map on actual homogeneous localizations for a coordinate
projection is the affine polynomial renaming on normalized charts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.HomogeneousLocalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Dehomogenization

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (i : Fin (m + 1))

def gradedRename : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n where
  __ := (MvPolynomial.rename j).toRingHom
  map_mem {d} {p} hp := (show MvPolynomial.IsHomogeneous p d from hp).rename_isHomogeneous

theorem gradedRename_X (a : Fin (m + 1)) : gradedRename j (MvPolynomial.X a) = MvPolynomial.X (j a) :=
  MvPolynomial.rename_X j a

theorem powers_le : Submonoid.powers (MvPolynomial.X i : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) ≤
    (Submonoid.powers (MvPolynomial.X (j i) : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)).comap (gradedRename j) := by
  rintro _ ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  change MvPolynomial.X (j i) ^ k = MvPolynomial.rename j (MvPolynomial.X i ^ k)
  rw [map_pow, MvPolynomial.rename_X]

def chartMap : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing m i →+* Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n (j i) :=
  HomogeneousLocalization.map (gradedRename j) (powers_le j i)

theorem chartMap_mk (k : ℕ) (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) (hp : p ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m (k • (1 : ℕ))) :
    chartMap j i (Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous m i) k p hp) =
      Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n (j i)) k (MvPolynomial.rename j p)
        ((show MvPolynomial.IsHomogeneous p (k • (1 : ℕ)) from hp).rename_isHomogeneous) := by
  apply HomogeneousLocalization.val_injective
  simp only [chartMap, Away.mk, HomogeneousLocalization.map_mk, map_pow, gradedRename_X]
  rfl

theorem chartMap_constants (c : ℂ) :
    chartMap j i (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartConstants m i c) = Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartConstants n (j i) c := by
  apply HomogeneousLocalization.val_injective
  simp [chartMap, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartConstants, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, gradedRename]

theorem chartMap_ratio (a : Fin (m + 1)) :
    chartMap j i (Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRatio m i a) = Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRatio n (j i) (j a) := by
  simpa only [Foundations.Scheme.PolynomialToProjectiveChart.projectiveChartRatio, MvPolynomial.rename_X] using
    chartMap_mk j i 1 (MvPolynomial.X a) (by simpa using Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous m a)

theorem polynomial_comp (hj : Function.Injective j) :
    (chartMap j i).comp (Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart m i) =
      (Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart n (j i)).comp (MvPolynomial.rename (Projection.Dehomogenization.omitted j hj i)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chartMap_constants]
  · intro a
    change chartMap j i (Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart m i (MvPolynomial.X a)) =
      Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart n (j i) (MvPolynomial.rename (Projection.Dehomogenization.omitted j hj i) (MvPolynomial.X a))
    rw [Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart_X, chartMap_ratio, MvPolynomial.rename_X, Foundations.Scheme.PolynomialToProjectiveChart.polynomialToProjectiveChart_X]
    rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming
