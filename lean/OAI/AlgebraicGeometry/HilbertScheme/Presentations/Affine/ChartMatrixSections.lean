import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates

/-! # Chart Matrix Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixSections.GradedHilbert

noncomputable section

/-! Passing from affine global sections to ring coefficients and back
recovers the actual normalized chart matrix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {R : Type u} [CommRing R]

theorem affineChartMatrix_map_sections (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of R) ⟶ S)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    (NormalizedHilbert.AffineCoordinates.GradedHilbert.affineChartMatrix a f x).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = Normalized.AtlasMaps.Grassmannian.chartMatrix a S x := by
  ext i j
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id (Normalized.AtlasMaps.Grassmannian.chartMatrix a S x i j)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixSections.GradedHilbert
