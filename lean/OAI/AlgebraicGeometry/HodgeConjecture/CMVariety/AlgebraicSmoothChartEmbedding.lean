import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicPeriodChartAlgebra
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.PeriodCone

/-! # Algebraic Smooth Chart Embedding -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicSmoothChartEmbedding.CM.Abelian.Algebraization.SmoothChartEmbedding

noncomputable section

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints

theorem exists_embedding (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : Φ.space) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      (∀ q ∈ Q, ∃ k, q.IsHomogeneous k) ∧
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} ∧
      ∀ i : Fin (n + 1), Algebra.Smooth ℂ (Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction.chart (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  obtain ⟨n, f, Q, hf, hd, hQ, heq⟩ := PeriodCone.CM.Abelian.Algebraization.AlgebraicPeriodCone.period_cone_homogeneous_equations Φ
  have hS (w) (hw : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) : w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    rw [heq]
    intro p hp
    apply hw p
    intro v hv
    rw [heq] at hv
    exact hv p hp
  exact ⟨n, f, Q, hf, hd, hQ, heq, fun i => AlgebraicPeriodChartAlgebra.CM.Abelian.Algebraization.PeriodChartAlgebra.smooth Φ f hf hd hS i⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicSmoothChartEmbedding.CM.Abelian.Algebraization.SmoothChartEmbedding
