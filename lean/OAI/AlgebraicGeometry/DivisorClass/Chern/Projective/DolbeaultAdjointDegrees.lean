import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.UnitaryForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarDolbeaultAdjoint

/-! # Dolbeault Adjoint Degrees -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DolbeaultAdjointDegrees

noncomputable section

/-! Actual scalar Dolbeault operators and their metric adjoints in every degree. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveFormPointPair_add_right (n : ℕ)
    (a b c : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a (b + c) x =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x + Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a c x := by
  calc
    _ = star (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (b + c) a x) :=
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm V n a (b + c) x).symm
    _ = star (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b a x + Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n c a x) := by
      rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_add_left]
    _ = _ := by rw [star_add, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm]

theorem projectiveFormPointPair_smul_right (n : ℕ)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (c : ℂ) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a (c • b) x = c * Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a b x := by
  calc
    _ = star (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (c • b) a x) :=
      (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm V n a (c • b) x).symm
    _ = star (star c * Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n b a x) := by
      rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_smul_left]
    _ = _ := by rw [star_mul, star_star, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_symm, mul_comm]

def projectiveScalarFormPart (n : ℕ) (z : ℂˣ) (c : ℂ) :
    Module.End ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :=
  (1 / 2 : ℂ) • (LinearMap.id + c • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z)

theorem projectiveScalarFormPart_point_pair (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (c : ℂ)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) :
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (projectiveScalarFormPart V n z c a).val b.val x =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val (projectiveScalarFormPart V n z⁻¹ (star c) b).val x := by
  change Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n ((1 / 2 : ℂ) • (a.val + c • Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z a.val)) b.val x =
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val ((1 / 2 : ℂ) • (b.val + star c • Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z⁻¹ b.val)) x
  rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_smul_left, Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_add_left,
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveFormPointPair_smul_left, projectiveFormPointPair_smul_right,
    projectiveFormPointPair_add_right, projectiveFormPointPair_smul_right,
    UnitaryForms.projectiveFormPointPair_action_adjoint V n z hz]
  simp only [star_div₀, star_one, star_ofNat]

theorem projectiveScalarFormPart_integral_pair (n : ℕ) (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (c : ℂ)
    (a b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n (projectiveScalarFormPart V n z c a) b =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n a (projectiveScalarFormPart V n z⁻¹ (star c) b) := by
  rw [MetricAdjoint.projectiveL2Pair_actualMetricIntegral, MetricAdjoint.projectiveL2Pair_actualMetricIntegral]
  exact integral_congr_ae (Filter.Eventually.of_forall (projectiveScalarFormPart_point_pair V n z hz c a b))

def projectiveScalarDolbeaultDegree (q : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (q + 1) :=
  (projectiveScalarFormPart V (q + 1) AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹)).comp
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d

def projectiveScalarDolbeaultDegreeAdjoint (q : ℕ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (q + 1) →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q :=
  (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V q).comp
    (projectiveScalarFormPart V (q + 1) AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit (star (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹)))

theorem projectiveScalarDolbeaultDegree_onOpen (q : ℕ) (U : Opens V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (projectiveScalarDolbeaultDegree V q a) =
      Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a) := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U ((1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a +
    (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹) • Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))) = _
  rw [map_smul, map_add, map_smul, ← Open.ManifoldAction.openManifoldComplexAction_onOpen, ← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d]
  rfl

theorem projectiveScalarDolbeaultDegreeAdjoint_pair (q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (q + 1)) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V (q + 1) b (projectiveScalarDolbeaultDegree V q a) =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V q (projectiveScalarDolbeaultDegreeAdjoint V q b) a := by
  have hz : ‖(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit : ℂ)‖ = 1 := by rw [AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe, Complex.norm_I]
  have h := projectiveScalarFormPart_integral_pair V (q + 1) AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit hz
    (star (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹)) b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)
  rw [star_star] at h
  exact h.symm.trans (Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair V q a _)

theorem projectiveScalarDolbeaultDegreeAdjoint_actualIntegral (q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (q + 1)) :
    (∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V (q + 1) b.val (projectiveScalarDolbeaultDegree V q a).val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      ∫ x, Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V q (projectiveScalarDolbeaultDegreeAdjoint V q b).val a.val x ∂ ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
  rw [← MetricAdjoint.projectiveL2Pair_actualMetricIntegral, ← MetricAdjoint.projectiveL2Pair_actualMetricIntegral]
  exact projectiveScalarDolbeaultDegreeAdjoint_pair V q a b

theorem projectiveScalarFormPart_zero_at (n : ℕ) (z : ℂˣ) (c : ℂ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (x : V.analyticSpace) (ha : a x = 0) :
    projectiveScalarFormPart V n z c a x = 0 := by
  change (1 / 2 : ℂ) • (a x + c • (a x).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x (↑z⁻¹ : ℂ))) = 0
  rw [ha]
  ext v
  change (1 / 2 : ℂ) * (0 + c * 0) = 0
  ring

theorem projectiveScalarDolbeaultDegreeAdjoint_zero_off_closed (q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (q + 1))
    {K : Set V.analyticSpace} (hK : IsClosed K) (ha : ∀ x, x ∉ K → a x = 0)
    {x : V.analyticSpace} (hx : x ∉ K) : projectiveScalarDolbeaultDegreeAdjoint V q a x = 0 :=
  Analysis.HodgeTheory.Decomposition.CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V q
    (projectiveScalarFormPart V (q + 1) AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit (star (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹)) a) hK
      (fun y hy => projectiveScalarFormPart_zero_at V (q + 1) AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit _ a y (ha y hy)) hx

theorem projectiveScalarDolbeaultDegree_apply (q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace q) (x : V.analyticSpace) :
    projectiveScalarDolbeaultDegree V q a x = (1 / 2 : ℂ) •
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x + (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹) •
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x Complex.I)) := by
  change (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x + (-(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultPrimeCharacter 0 q)⁻¹) •
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x).compContinuousLinearMap (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x (↑(AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹)⁻¹ : ℂ))) = _
  rw [inv_inv, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DolbeaultAdjointDegrees
