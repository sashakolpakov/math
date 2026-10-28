import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FormOrthogonality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OneFormProjection
import OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport

/-! # Scalar Dolbeault Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarDolbeaultAdjoint

noncomputable section

/-! The genuine scalar Dolbeault adjoint, with the original metric integral
identity and a proved support law. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport.Constructions
attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def projectiveScalarOnePart (c : ℂ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1 →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1 :=
  (1 / 2 : ℂ) • (LinearMap.id + c • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)

theorem projectiveScalarOnePart_onOpen (c : ℂ) (U : Opens V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (projectiveScalarOnePart V c a) =
      Manifold.OneFormProjection.openManifoldOnePart c (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a) := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U ((1 / 2 : ℂ) •
    (a + c • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a)) = _
  rw [map_smul, map_add, map_smul, ← Open.ManifoldAction.openManifoldComplexAction_onOpen]
  rfl

theorem projectiveScalarOnePart_point_pair
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 (projectiveScalarOnePart V Complex.I a).val b.val x =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val (projectiveScalarOnePart V Complex.I b).val x := by
  have h := Open.FormOrthogonality.projectiveOpenFormPair_anti_selfAdjoint V
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ b) ⟨x, trivial⟩
  rw [← projectiveScalarOnePart_onOpen, ← projectiveScalarOnePart_onOpen] at h
  rw [CovectorPair.projectiveFormPointPair_eq_tangentPair, CovectorPair.projectiveFormPointPair_eq_tangentPair]
  exact h

theorem projectiveScalarOnePart_integral_pair
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 (projectiveScalarOnePart V Complex.I a) b =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a (projectiveScalarOnePart V Complex.I b) := by
  rw [MetricAdjoint.projectiveL2Pair_actualMetricIntegral, MetricAdjoint.projectiveL2Pair_actualMetricIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (projectiveScalarOnePart_point_pair V a b)

def projectiveScalarDolbeaultZero :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1 :=
  (projectiveScalarOnePart V Complex.I).comp Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

theorem projectiveScalarDolbeaultZero_onOpen (U : Opens V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (projectiveScalarDolbeaultZero V a) =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a) := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (projectiveScalarOnePart V Complex.I (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)) = _
  rw [projectiveScalarOnePart_onOpen, ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, Manifold.OneFormProjection.openManifoldOnePart_d]

def projectiveScalarDolbeaultAdjoint :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1 →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
  (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V 0).comp (projectiveScalarOnePart V Complex.I)

theorem projectiveScalarDolbeaultAdjoint_pair
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 b (projectiveScalarDolbeaultZero V a) =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 0 (projectiveScalarDolbeaultAdjoint V b) a := by
  change Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 b (projectiveScalarOnePart V Complex.I (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)) = _
  rw [← projectiveScalarOnePart_integral_pair, Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair]
  rfl

theorem projectiveScalarDolbeaultAdjoint_actualIntegral
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) :
    (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 b.val (projectiveScalarDolbeaultZero V a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 0 (projectiveScalarDolbeaultAdjoint V b).val a.val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  rw [← MetricAdjoint.projectiveL2Pair_actualMetricIntegral, ← MetricAdjoint.projectiveL2Pair_actualMetricIntegral]
  exact projectiveScalarDolbeaultAdjoint_pair V a b

theorem projectiveScalarOnePart_zero_at (c : ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) (x : V.analyticSpace) (ha : a x = 0) :
    projectiveScalarOnePart V c a x = 0 := by
  have h := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel ⊤ 1 => b ⟨x, trivial⟩)
    (projectiveScalarOnePart_onOpen V c ⊤ a)
  rw [Holomorphic.OneFormProjection.openManifoldOnePart_apply] at h
  change projectiveScalarOnePart V c a x = (1 / 2 : ℂ) • (a x + c •
    (a x).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x Complex.I)) at h
  rw [h, ha]
  ext v
  change (1 / 2 : ℂ) * (0 + c * 0) = 0
  ring

theorem projectiveScalarDolbeaultAdjoint_zero_off_closed
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    {K : Set V.analyticSpace} (hK : IsClosed K) (ha : ∀ x, x ∉ K → a x = 0)
    {x : V.analyticSpace} (hx : x ∉ K) : projectiveScalarDolbeaultAdjoint V a x = 0 :=
  Analysis.HodgeTheory.Decomposition.CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V 0 (projectiveScalarOnePart V Complex.I a) hK
    (fun y hy => projectiveScalarOnePart_zero_at V Complex.I a y (ha y hy)) hx

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarDolbeaultAdjoint
