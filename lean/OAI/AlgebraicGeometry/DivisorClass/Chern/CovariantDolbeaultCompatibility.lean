import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovariantDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero

/-! # Covariant Dolbeault Compatibility -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual metric connection induces exactly the original holomorphic Dolbeault operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {U : Opens M}

theorem CovariantDolbeaultCompatibility.openManifoldOnePart_scalar_mul (c : ℂ) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Manifold.OneFormProjection.openManifoldOnePart c (SmoothScalarForm.smoothScalarOpenFormMul f a) =
      SmoothScalarForm.smoothScalarOpenFormMul f (Manifold.OneFormProjection.openManifoldOnePart c a) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Holomorphic.OneFormProjection.openManifoldOnePart_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply,
    SmoothScalarForm.smoothScalarOpenFormMul_apply, Holomorphic.OneFormProjection.openManifoldOnePart_apply]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
  ring

theorem CovariantDolbeaultCompatibility.openManifoldOnePart_anti_holo_zero (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Manifold.OneFormProjection.openManifoldOnePart Complex.I (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a) = 0 := by
  have he := congrArg (Manifold.OneFormProjection.openManifoldOnePart Complex.I) (Manifold.OneFormProjection.openManifoldOnePart_add a)
  rw [map_add, Holomorphic.OneFormProjection.openManifoldOnePart_eq_of_anti _ (Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic a)] at he
  exact add_eq_right.mp he

theorem CovariantDolbeaultCompatibility.openConnectionDerivative_antiholomorphic (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (hA : Manifold.OneFormProjection.openManifoldOnePart Complex.I A = 0) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    Manifold.OneFormProjection.openManifoldOnePart Complex.I (SmoothScalarExterior.openConnectionDerivative A a) = Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a := by
  change Manifold.OneFormProjection.openManifoldOnePart Complex.I
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a + SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A) = _
  rw [map_add, Manifold.OneFormProjection.openManifoldOnePart_d, CovariantDolbeaultCompatibility.openManifoldOnePart_scalar_mul, hA, map_zero, add_zero]

variable {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.localConnection_antiholomorphic (i : M) :
    Manifold.OneFormProjection.openManifoldOnePart Complex.I (h.localConnection i) = 0 :=
  CovariantDolbeaultCompatibility.openManifoldOnePart_anti_holo_zero (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (h.logFunction i)))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_dolbeault (U : Opens M)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    Holomorphic.OneFormProjection.holomorphicLineOnePart u U Complex.I (h.covariantDerivative U a) = HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u U a := by
  apply Subtype.ext
  funext i
  change Manifold.OneFormProjection.openManifoldOnePart Complex.I
    (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)) (a.val i)) = _
  apply CovariantDolbeaultCompatibility.openConnectionDerivative_antiholomorphic
  rw [← Manifold.OneFormProjection.openManifoldOnePart_restrict, h.localConnection_antiholomorphic, map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
