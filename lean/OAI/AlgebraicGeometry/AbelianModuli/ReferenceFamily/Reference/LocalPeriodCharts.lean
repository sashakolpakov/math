import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Local Period Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Explicit local vector lifts of the actual native period comparison.
Their smoothness and inverse equations come from its constructed atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.localPeriodCharts_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.localPeriodCharts_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def AlgebraicModel.ReferenceAlgebraicModel.localPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  ⟨M.period.symm ⁻¹' (F.periodData.periodChart (M.period.symm p)).source,
    (F.periodData.periodChart (M.period.symm p)).open_source.preimage M.period.symm.continuous⟩

def AlgebraicModel.ReferenceAlgebraicModel.localPeriodLift (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) : F.periodData.space :=
  F.periodData.periodChart (M.period.symm p) (M.period.symm q)

theorem AlgebraicModel.ReferenceAlgebraicModel.mem_localPeriodDomain (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    p ∈ M.localPeriodDomain p := F.periodData.mem_periodChart_source (M.period.symm p)

theorem AlgebraicModel.ReferenceAlgebraicModel.localPeriodLift_period (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (hq : q ∈ M.localPeriodDomain p) : M.vectorPeriod (M.localPeriodLift p q) = q := by
  have h := (F.periodData.periodChart (M.period.symm p)).left_inv hq
  rw [F.periodData.periodChart_symm] at h
  exact (congrArg M.period h).trans (M.period.apply_symm_apply q)

theorem AlgebraicModel.ReferenceAlgebraicModel.localPeriodLift_contMDiffAt (p q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (hq : q ∈ M.localPeriodDomain p) :
    ContMDiffAt 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space) ∞
      (M.localPeriodLift p) q := by
  have hc : ContMDiffAt 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, F.periodData.space) ∞
      (F.periodData.periodChart (M.period.symm p)) (M.period.symm q) :=
    (contMDiffOn_chart (I := 𝓘(ℂ, F.periodData.space)) (x := M.period.symm p)).contMDiffAt
      ((F.periodData.periodChart (M.period.symm p)).open_source.mem_nhds hq)
  exact hc.comp q (M.period.symm.contMDiff q)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
