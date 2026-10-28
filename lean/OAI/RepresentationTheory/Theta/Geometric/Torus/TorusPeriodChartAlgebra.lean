import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartSmoothness
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness

/-! # Torus Period Chart Algebra -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartAlgebra.CM.Algebraization.PeriodChartAlgebra

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {n : ℕ}

theorem smooth (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
      Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))
    (hS : ∀ w, (∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) → w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (i : Fin (n + 1)) :
    Algebra.Smooth ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  let S := Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i
  let : Algebra.FinitePresentation ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian _)
  apply Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness.Constructions.SmoothFromComplexPoints.smooth
  intro q
  let x := Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinates S q
  have hx : x ∈ S := Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinates_mem S
    (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart_determined_by_polynomials (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) hS i) q
  have hsm := TorusPeriodChartSmoothness.CM.Algebraization.PeriodChartSmoothness.mem_smoothLocus Φ f hf hd hS i x hx
  have heq : Geometry.ComplexTorus.RiemannProjectivity.AffineCone.Constructions.AffineCoordinateSmoothness.point S x hx = q := by
    apply Ideal.Quotient.algHom_ext ℂ
    apply AlgHom.ext
    intro p
    change MvPolynomial.eval x p = q (Ideal.Quotient.mk _ p)
    exact Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.eval_coordinates S q p
  rwa [heq] at hsm

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartAlgebra.CM.Algebraization.PeriodChartAlgebra
