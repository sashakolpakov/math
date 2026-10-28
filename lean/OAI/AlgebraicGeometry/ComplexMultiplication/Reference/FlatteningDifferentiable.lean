import OAI.AlgebraicGeometry.ClosedImmersion.HolomorphicChartsAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Flattening Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FlatteningDifferentiable

noncomputable section

/-! # Differentiability of the unchanged original holomorphic flattening chart -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped _root_.Manifold

theorem biAnalyticRestrict_mDifferentiable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (e : OpenPartialHomeomorph E F) :
    (ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) := by
  constructor
  · intro x hx
    exact ((ClosedImmersion.HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff e x).mp hx).2.1
      |>.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  · intro y hy
    have hx := (ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).map_target hy
    have ha := ((ClosedImmersion.HolomorphicChartsAt.OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff e _).mp hx).2.2
    change AnalyticAt ℂ e.symm ((ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e) ((ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).symm y)) at ha
    rw [(ClosedImmersion.HolomorphicCharts.OpenPartialHomeomorph.biAnalyticRestrict e).right_inv hy] at ha
    exact ha.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt

theorem mDifferentiable_restrOpen
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N]
    (e : OpenPartialHomeomorph M N)
    (he : e.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F)) (U : Set M) (hU : IsOpen U) :
    (e.restrOpen U hU).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) := by
  constructor
  · intro x hx
    exact (he.mdifferentiableAt hx.1).mdifferentiableWithinAt
  · intro y hy
    exact (he.mdifferentiableAt_symm hy.1).mdifferentiableWithinAt

theorem originalFlatteningChart_mDifferentiable
    (X Y : Over (Spec (.of ℂ))) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionHolomorphicFlatteningChart X Y i m d z).MDifferentiable
      𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) := by
  apply mDifferentiable_restrOpen
  exact (mdifferentiable_chart (I := 𝓘(ℂ, Fin d → ℂ)) (ComplexPoint.Basic.Point.map i z)).trans
    (biAnalyticRestrict_mDifferentiable (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalCoordinateChange X Y i m d z))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FlatteningDifferentiable
