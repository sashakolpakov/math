import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodChartAlgebra
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusAlgebraicPeriodCone

/-! # Torus Smooth Chart Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusSmoothChartEmbedding.CM.Algebraization.SmoothChartEmbedding

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints

theorem exists_embedding (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : Φ.space) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      (∀ q ∈ Q, ∃ k, q.IsHomogeneous k) ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} ∧
      ∀ i : Fin (n + 1), Algebra.Smooth ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  obtain ⟨n, f, Q, hf, hd, hQ, heq⟩ := TorusAlgebraicPeriodCone.CM.Algebraization.AlgebraicPeriodCone.period_cone_homogeneous_equations Φ
  have hS (w) (hw : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) : w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    rw [heq]
    intro p hp
    apply hw p
    intro v hv
    rw [heq] at hv
    exact hv p hp
  exact ⟨n, f, Q, hf, hd, hQ, heq, fun i => TorusPeriodChartAlgebra.CM.Algebraization.PeriodChartAlgebra.smooth Φ f hf hd hS i⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusSmoothChartEmbedding.CM.Algebraization.SmoothChartEmbedding
