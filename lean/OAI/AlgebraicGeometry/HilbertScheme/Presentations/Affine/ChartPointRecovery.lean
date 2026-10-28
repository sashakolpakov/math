import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixSections

/-! # Chart Point Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPointRecovery.GradedHilbert

noncomputable section

/-! The ring-coefficient matrix of an affine chart point recovers the
actual chart morphism over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {R : Type u} [CommRing R]

theorem affineNormalizedChartPoint_of_affineChartMatrix
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of R) ⟶ S)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a (NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix a f x) (NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix_normalized a f x) = x := by
  apply Normalized.AtlasMaps.Grassmannian.chartMatrix_injective a S (Over.mk f)
  rw [NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint_matrix]
  exact ChartMatrixSections.GradedHilbert.affineChartMatrix_map_sections a f x

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPointRecovery.GradedHilbert
