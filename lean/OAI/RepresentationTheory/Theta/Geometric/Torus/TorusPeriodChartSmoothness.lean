import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusNormalizedConeSmoothness
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness

/-! # Torus Period Chart Smoothness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartSmoothness.CM.Algebraization.PeriodChartSmoothness

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction
  Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {n : ℕ}

theorem mem_smoothLocus (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (i : Fin (n + 1)) (x : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (hx : x ∈ Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) :
    Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) x hx) ∈
      Algebra.smoothLocus ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  apply Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.ConeChartSmoothness.mem_smoothLocus (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) i x hx
  let v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := ⟨AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x, hx⟩
  have hvi : v.val i = 1 := AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_self i x
  have hvi0 : v.val i ≠ 0 := hvi ▸ one_ne_zero
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.mem_projectiveCone_iff_dehomogenize (range f) i v.val hvi0).mp v.property
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  have htarget : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).target := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target]
    trivial
  have hfp : f (QuotientAddGroup.mk z) = (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val) := by
    rw [hz]
    exact ht
  have hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source := by
    rw [hfp]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm.map_source htarget
  have hchart : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z)) = AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val := by
    rw [hfp]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).right_inv htarget
  have hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1) := by
    symm
    change Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate i (1, (1 : ℂ) • AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z))) = v.val
    rw [hchart, ← hvi]
    exact Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate_dehomogenize i v.val hvi0
  exact TorusNormalizedConeSmoothness.CM.Algebraization.NormalizedConeSmoothness.mem_smoothLocus_at_parameter Φ f hf hd i z hi v hv

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartSmoothness.CM.Algebraization.PeriodChartSmoothness
