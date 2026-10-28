import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AlgebraicPeriod

/-! # Smooth Chart -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothChart.Constructions.SmoothChartEmbedding

noncomputable section

/-! # RiemannProjectivity: the projective period embedding has smooth genuine affine chart algebras -/

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeChartBy.Constructions.ConeChartRestriction OAI.Geometry.ComplexTorus.RiemannProjectivity.AffineVanishing.Constructions.AffineVanishingPoints

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem exists_embedding (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (Q : Finset (MvPolynomial (Fin (n + 1)) ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      (∀ q ∈ Q, ∃ k, q.IsHomogeneous k) ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} ∧
      ∀ i : Fin (n + 1), Algebra.Smooth ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing (ConeChartBy.Constructions.ConeChartRestriction.chart (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) i)) := by
  obtain ⟨n, f, Q, hf, hd, hQ, heq⟩ := AlgebraicPeriod.Constructions.AlgebraicPeriodCone.period_cone_homogeneous_equations hRiemannProjectivity Φ
  have hS (w) (hw : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) : w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    rw [heq]
    intro p hp
    apply hw p
    intro v hv
    rw [heq] at hv
    exact hv p hp
  exact ⟨n, f, Q, hf, hd, hQ, heq, fun i => ChartPeriodSmoothness.Constructions.PeriodChartAlgebra.smooth Φ f hf hd hS i⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothChart.Constructions.SmoothChartEmbedding
