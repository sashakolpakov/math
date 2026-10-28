import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Curvature

/-! # Metric Twists -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The actual metric on the sum bundle has exactly the sum of the input curvatures. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  (u v : Holomorphic.Connecting.holomorphicUnitCohomology E M)

omit [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem Holomorphic.MetricTwists.holomorphicTensorMetric_log_difference
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) (x : Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    h.logFunction i ⟨x.val, x.property.2.1⟩ + k.logFunction i ⟨x.val, x.property.2.2⟩ -
      (Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).logFunction i ⟨x.val, x.property.1⟩ =
      (Real.log (Complex.normSq ((Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val x)) : ℂ) := by
  change (Real.log (h.weight i ⟨x.val, x.property.2.1⟩) : ℂ) +
    (Real.log (k.weight i ⟨x.val, x.property.2.2⟩) : ℂ) -
      (Real.log ((Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).weight i ⟨x.val, x.property.1⟩) : ℂ) = _
  rw [Holomorphic.TensorMetric.holomorphicTensorMetricWithReference_weight, Holomorphic.TensorMetric.holomorphicTensorMetricLocalWeight,
    Real.log_div (ne_of_gt (mul_pos (h.positive i _) (k.positive i _)))
      (ne_of_gt (Complex.normSq_pos.mpr (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero (Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v i) x))),
    Real.log_mul (ne_of_gt (h.positive i _)) (ne_of_gt (k.positive i _)), Complex.ofReal_sub, Complex.ofReal_add]
  ring

theorem Holomorphic.MetricTwists.holomorphicTensorMetricWithReference_localCurvature
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M (u + v) i from inf_le_left)
      ((Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).localCurvature i) =
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i from inf_le_right.trans inf_le_left) (h.localCurvature i) +
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M v i from inf_le_right.trans inf_le_right) (k.localCurvature i) := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.localCurvature
  rw [ScalarOpenConnection.smoothScalarOpenCurvature_restrict, ScalarOpenConnection.smoothScalarOpenCurvature_restrict, ScalarOpenConnection.smoothScalarOpenCurvature_restrict]
  exact (LogNormCurvatureVanishing.smoothScalarOpenCurvature_eq_of_logNormSq_difference (Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v i)
    (SmoothScalarForm.smoothComplexOpenFunctionRestrict (inf_le_right.trans inf_le_left) (h.logFunction i) +
      SmoothScalarForm.smoothComplexOpenFunctionRestrict (inf_le_right.trans inf_le_right) (k.logFunction i))
    (SmoothScalarForm.smoothComplexOpenFunctionRestrict inf_le_left ((Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).logFunction i))
    (Holomorphic.MetricTwists.holomorphicTensorMetric_log_difference u v h k r i)).symm.trans (ScalarOpenConnection.smoothScalarOpenCurvature_add _ _)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.curvature_onSubopen {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (i : M) (W : Opens M) (hW : W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen W h.curvature = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hW (h.localCurvature i) := by
  rw [← h.curvature_onOpen i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen]

theorem Holomorphic.MetricTwists.holomorphicTensorMetricWithReference_curvature
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) :
    (Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).curvature = h.curvature + k.curvature := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x)
      (Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).curvature =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) h.curvature +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) k.curvature := by
    exact ((Holomorphic.TensorMetric.holomorphicTensorMetricWithReference u v h k r).curvature_onSubopen x
      (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) inf_le_left).trans
      ((Holomorphic.MetricTwists.holomorphicTensorMetricWithReference_localCurvature u v h k r x).trans
        (congrArg₂ (fun a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) 2 => a + b)
          (h.curvature_onSubopen x (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) (inf_le_right.trans inf_le_left)).symm
          (k.curvature_onSubopen x (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) (inf_le_right.trans inf_le_right)).symm))
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v x) 2 =>
    a ⟨x, Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain_mem E M u v x⟩) he

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

theorem Holomorphic.MetricTwists.holomorphicTensorMetric_curvature (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v) :
    (Holomorphic.TensorMetric.holomorphicTensorMetric u v h k).curvature = h.curvature + k.curvature :=
  Holomorphic.MetricTwists.holomorphicTensorMetricWithReference_curvature u v h k (HolomorphicMetric.Data.holomorphicLineCanonicalMetric (u + v))

theorem Holomorphic.MetricTwists.holomorphicCanonicalTensorMetric_curvature :
    (Holomorphic.TensorMetric.holomorphicTensorMetric u v (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u) (HolomorphicMetric.Data.holomorphicLineCanonicalMetric v)).curvature =
      Holomorphic.GlobalCurvature.holomorphicLineGlobalCurvature u + Holomorphic.GlobalCurvature.holomorphicLineGlobalCurvature v := by
  rw [Holomorphic.MetricTwists.holomorphicTensorMetric_curvature, HolomorphicMetric.Curvature.holomorphicLineCanonicalMetric_curvature,
    HolomorphicMetric.Curvature.holomorphicLineCanonicalMetric_curvature]

end

/-! Actual metrics on all repeated sum-bundle twists, with their exact global curvature. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def HolomorphicMetric.Data.HolomorphicLineMetricData.cast {u v : Holomorphic.Connecting.holomorphicUnitCohomology E M}
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (e : u = v) : HolomorphicMetric.Data.HolomorphicLineMetricData v := e ▸ h

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cast_curvature {u v : Holomorphic.Connecting.holomorphicUnitCohomology E M}
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (e : u = v) : (h.cast e).curvature = h.curvature := by
  cases e
  rfl

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
  (u v : Holomorphic.Connecting.holomorphicUnitCohomology E M)

def Holomorphic.MetricTwists.holomorphicMetricTwist (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v) :
    (n : ℕ) → HolomorphicMetric.Data.HolomorphicLineMetricData (u + n • v)
  | 0 => h.cast (by rw [zero_nsmul, add_zero])
  | n + 1 => (Holomorphic.TensorMetric.holomorphicTensorMetric (u + n • v) v (holomorphicMetricTwist h k n) k).cast
      (by rw [succ_nsmul, add_assoc])

theorem Holomorphic.MetricTwists.holomorphicMetricTwist_curvature (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (n : ℕ) : (Holomorphic.MetricTwists.holomorphicMetricTwist u v h k n).curvature = h.curvature + n • k.curvature := by
  induction n with
  | zero => rw [Holomorphic.MetricTwists.holomorphicMetricTwist, HolomorphicMetric.Data.HolomorphicLineMetricData.cast_curvature, zero_nsmul, add_zero]
  | succ n ih =>
    rw [Holomorphic.MetricTwists.holomorphicMetricTwist, HolomorphicMetric.Data.HolomorphicLineMetricData.cast_curvature, Holomorphic.MetricTwists.holomorphicTensorMetric_curvature,
      ih, succ_nsmul, add_assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
