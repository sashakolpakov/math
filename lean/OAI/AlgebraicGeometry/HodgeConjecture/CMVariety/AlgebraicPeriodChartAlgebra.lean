import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusManifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness

/-! # Algebraic Period Chart Algebra -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartAlgebra.CM.Abelian.Algebraization.PeriodChartAlgebra

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {n : ℕ}

theorem smooth (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (i : Fin (n + 1)) :
    Algebra.Smooth ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  let S := Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i
  let : Algebra.FinitePresentation ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian _)
  apply Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.SmoothFromComplexPoints.smooth
  intro q
  let x := Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinates S q
  have hx : x ∈ S := Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinates_mem S
    (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart_determined_by_polynomials (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS i) q
  have hsm := AlgebraicPeriodChartSmoothness.CM.Abelian.Algebraization.PeriodChartSmoothness.mem_smoothLocus Φ f hf hd hS i x hx
  have heq : Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point S x hx = q := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply AlgHom.ext
    intro p
    change MvPolynomial.eval x p = q (Ideal.Quotient.mk _ p)
    exact Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.eval_coordinates S q p
  rwa [heq] at hsm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartAlgebra.CM.Abelian.Algebraization.PeriodChartAlgebra
