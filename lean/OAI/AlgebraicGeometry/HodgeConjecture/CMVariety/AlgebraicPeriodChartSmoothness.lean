import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicNormalizedConeSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness

/-! # Algebraic Period Chart Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartSmoothness.CM.Abelian.Algebraization.PeriodChartSmoothness

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction
  Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

variable {n : ℕ}

theorem mem_smoothLocus (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (i : Fin (n + 1)) (x : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (hx : x ∈ Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) :
    Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization.pointPrime (Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i) x hx) ∈
      Algebra.smoothLocus ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  apply Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.ConeChartSmoothness.mem_smoothLocus (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) i x hx
  let v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := ⟨Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i x, hx⟩
  have hvi : v.val i = 1 := Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_self i x
  have hvi0 : v.val i ≠ 0 := hvi ▸ one_ne_zero
  obtain ⟨t, ht⟩ := (ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.mem_projectiveCone_iff_dehomogenize (range f) i v.val hvi0).mp v.property
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  have htarget : ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).target := by
    rw [ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target]
    trivial
  have hfp : f (QuotientAddGroup.mk z) = (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val) := by
    rw [hz]
    exact ht
  have hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source := by
    rw [hfp]
    exact (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm.map_source htarget
  have hchart : ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z)) = ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v.val := by
    rw [hfp]
    exact (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).right_inv htarget
  have hv : v.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, 1) := by
    symm
    change Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate i (1, (1 : ℂ) • ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z))) = v.val
    rw [hchart, ← hvi]
    exact Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate_dehomogenize i v.val hvi0
  exact AlgebraicNormalizedConeSmoothness.CM.Abelian.Algebraization.NormalizedConeSmoothness.mem_smoothLocus_at_parameter Φ f hf hd i z hi v hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartSmoothness.CM.Abelian.Algebraization.PeriodChartSmoothness
