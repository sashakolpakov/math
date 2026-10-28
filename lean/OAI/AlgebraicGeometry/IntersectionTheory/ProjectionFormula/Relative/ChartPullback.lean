import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartX
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ScalarPullback

/-! # Chart Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartPullback

noncomputable section

/-! Coefficient specialization pulls back each actual projective
coordinate chart to the same polynomial chart over the new coefficients. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartX.Projective
open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear (space grading)

theorem range_chart (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Set.range (ChartX.Projective.projectiveAffineChartMap R n i) = (ProjectiveI.Chart.projectiveCoordinateOpen R n i : Set (ProjectiveLinear.space R n)) := by
  change Set.range ((ProjectiveI.Chart.projectiveCoordinateOpen R n i).ι ∘ (ChartX.Projective.projectiveCoordinateIsoSpec R n i).inv) = _
  rw [Set.range_comp, (ChartX.Projective.projectiveCoordinateIsoSpec R n i).inv.surjective.range_eq, Set.image_univ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def cover (R : Type) [CommRing R] (n : ℕ) : (ProjectiveLinear.space R n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (n + 1))
    (fun i => Spec (.of (ProjectiveChart.projectiveChartPolynomial R n i)))
    (ChartX.Projective.projectiveAffineChartMap R n) (by
      intro x
      obtain ⟨i, hi⟩ := ProjectiveI.Chart.exists_mem_projectiveCoordinateOpen R n x
      obtain ⟨y, hy⟩ := (Set.ext_iff.mp (range_chart R n i) x).mpr hi
      exact ⟨i, y, hy⟩) (fun _ => inferInstance)

theorem chart {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := {j : Fin (n + 1) // j ≠ i}) f)))
      (ChartX.Projective.projectiveAffineChartMap S n i) (ChartX.Projective.projectiveAffineChartMap R n i)
      (ProjectiveI.Scalars.map f n) := by
  apply IsOpenImmersion.isPullback
  · exact ChartX.ScalarMap.chart f n i
  · apply SetLike.coe_injective
    change ProjectiveI.Scalars.map f n ⁻¹' Set.range (ChartX.Projective.projectiveAffineChartMap R n i) =
      Set.range (ChartX.Projective.projectiveAffineChartMap S n i)
    rw [range_chart, range_chart]
    ext x
    change MvPolynomial.X i ∉ ((ProjectiveI.Scalars.map f n) x).asHomogeneousIdeal ↔
      MvPolynomial.X i ∉ x.asHomogeneousIdeal
    change ProjectiveI.Scalars.graded f n (MvPolynomial.X i) ∉ x.asHomogeneousIdeal ↔ _
    rw [ChartX.ScalarMap.graded_X]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ChartPullback
