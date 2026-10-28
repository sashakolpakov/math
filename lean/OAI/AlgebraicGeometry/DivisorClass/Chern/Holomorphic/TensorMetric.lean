import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorGaugeTransitions

/-! # Tensor Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorMetric

noncomputable section

/-! The actual local gauges construct a product metric on the original sum bundle. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem gaugeMetricProduct_transition (c a b i j x y : ℝ)
    (hi : i ≠ 0) (hj : j ≠ 0) (h : c * i = j * a * b) :
    (a * x) * (b * y) / i = c * (x * y / j) := by
  field_simp
  linear_combination -(x * y) * h

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  (u v : Connecting.holomorphicUnitCohomology E M)

def holomorphicTensorMetricLocalWeight (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) : ℝ :=
  h.weight i ⟨x.val, x.property.2.1⟩ * k.weight i ⟨x.val, x.property.2.2⟩ /
    Complex.normSq ((TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val x)

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricLocalWeight_positive
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    0 < holomorphicTensorMetricLocalWeight u v h k i x :=
  div_pos (mul_pos (h.positive i _) (k.positive i _)) (Complex.normSq_pos.mpr
    (SlitLog.holomorphicUnit_value_ne_zero (TensorGaugeTransitions.holomorphicTensorGauge E M u v i) x))

theorem holomorphicTensorMetricLocalWeight_smooth
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v) (i : M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (holomorphicTensorMetricLocalWeight u v h k i) := by
  have ha := (h.smooth i).comp (contMDiff_inclusion (I := 𝓘(ℝ, E))
    (show TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤ CohomologyTransitions.holomorphicCohomologyDomain E M u i from
      inf_le_right.trans inf_le_left))
  have hb := (k.smooth i).comp (contMDiff_inclusion (I := 𝓘(ℝ, E))
    (show TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤ CohomologyTransitions.holomorphicCohomologyDomain E M v i from
      inf_le_right.trans inf_le_right))
  have hg := HolomorphicLine.HermitianPair.complexNormSq_contDiff.contMDiff.comp
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val.property)
  intro x
  exact ((ha x).mul (hb x)).mul
    ((contDiffAt_inv ℝ (ne_of_gt (Complex.normSq_pos.mpr
      (SlitLog.holomorphicUnit_value_ne_zero (TensorGaugeTransitions.holomorphicTensorGauge E M u v i) x)))).contMDiffAt.comp x (hg x))

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricLocalWeight_transition
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (i j x : M) (hi : x ∈ TensorGaugeTransitions.holomorphicTensorDomain E M u v i)
    (hj : x ∈ TensorGaugeTransitions.holomorphicTensorDomain E M u v j) :
    holomorphicTensorMetricLocalWeight u v h k i ⟨x, hi⟩ =
      Complex.normSq ((CohomologyTransitions.holomorphicCohomologyTransition E M (u + v) i j).val ⟨x, hi.1, hj.1⟩) *
        holomorphicTensorMetricLocalWeight u v h k j ⟨x, hj⟩ := by
  have hg := congrArg Complex.normSq (TensorGaugeTransitions.holomorphicTensorGauge_transition E M u v i j x hi hj)
  simp only [Complex.normSq_mul] at hg
  unfold holomorphicTensorMetricLocalWeight
  rw [h.transition i j x hi.2.1 hj.2.1, k.transition i j x hi.2.2 hj.2.2]
  exact gaugeMetricProduct_transition _ _ _ _ _ _ _
    (ne_of_gt (Complex.normSq_pos.mpr (SlitLog.holomorphicUnit_value_ne_zero
      (TensorGaugeTransitions.holomorphicTensorGauge E M u v i) ⟨x, hi⟩)))
    (ne_of_gt (Complex.normSq_pos.mpr (SlitLog.holomorphicUnit_value_ne_zero
      (TensorGaugeTransitions.holomorphicTensorGauge E M u v j) ⟨x, hj⟩))) hg

def holomorphicTensorMetricLocalRatio (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) : ℝ :=
  holomorphicTensorMetricLocalWeight u v h k i x / r.weight i ⟨x.val, x.property.1⟩

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricLocalRatio_positive
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    0 < holomorphicTensorMetricLocalRatio u v h k r i x :=
  div_pos (holomorphicTensorMetricLocalWeight_positive u v h k i x) (r.positive i _)

theorem holomorphicTensorMetricLocalRatio_smooth
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (holomorphicTensorMetricLocalRatio u v h k r i) := by
  have hr := (r.smooth i).comp (contMDiff_inclusion (I := 𝓘(ℝ, E))
    (show TensorGaugeTransitions.holomorphicTensorDomain E M u v i ≤ CohomologyTransitions.holomorphicCohomologyDomain E M (u + v) i from inf_le_left))
  intro x
  exact (holomorphicTensorMetricLocalWeight_smooth u v h k i x).mul
    ((contDiffAt_inv ℝ (ne_of_gt (r.positive i _))).contMDiffAt.comp x (hr x))

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricLocalRatio_overlap
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i j x : M)
    (hi : x ∈ TensorGaugeTransitions.holomorphicTensorDomain E M u v i) (hj : x ∈ TensorGaugeTransitions.holomorphicTensorDomain E M u v j) :
    holomorphicTensorMetricLocalRatio u v h k r i ⟨x, hi⟩ =
      holomorphicTensorMetricLocalRatio u v h k r j ⟨x, hj⟩ := by
  unfold holomorphicTensorMetricLocalRatio
  rw [holomorphicTensorMetricLocalWeight_transition u v h k i j x hi hj, r.transition i j x hi.1 hj.1]
  exact mul_div_mul_left _ _ (ne_of_gt (Complex.normSq_pos.mpr
    (SlitLog.holomorphicUnit_value_ne_zero (CohomologyTransitions.holomorphicCohomologyTransition E M (u + v) i j) ⟨x, hi.1, hj.1⟩)))

def holomorphicTensorMetricRatio (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) : M → ℝ :=
  SmoothCoverFunctions.smoothCoverFunction (TensorGaugeTransitions.holomorphicTensorDomain E M u v) (TensorGaugeTransitions.holomorphicTensorDomain_mem E M u v)
    (holomorphicTensorMetricLocalRatio u v h k r)

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricRatio_onOpen
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    holomorphicTensorMetricRatio u v h k r x.val = holomorphicTensorMetricLocalRatio u v h k r i x :=
  SmoothCoverFunctions.smoothCoverFunction_onOpen _ _ _ (holomorphicTensorMetricLocalRatio_overlap u v h k r) i x

theorem holomorphicTensorMetricRatio_smooth
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (holomorphicTensorMetricRatio u v h k r) :=
  SmoothCoverFunctions.smoothCoverFunction_contMDiff _ _ _ (holomorphicTensorMetricLocalRatio_overlap u v h k r)
    (holomorphicTensorMetricLocalRatio_smooth u v h k r)

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicTensorMetricRatio_positive
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (x : M) : 0 < holomorphicTensorMetricRatio u v h k r x :=
  SmoothCoverFunctions.smoothCoverFunction_pos _ _ _ (holomorphicTensorMetricLocalRatio_positive u v h k r) x

def holomorphicTensorMetricWithReference (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v) :=
  r.rescale (holomorphicTensorMetricRatio u v h k r) (holomorphicTensorMetricRatio_smooth u v h k r)
    (holomorphicTensorMetricRatio_positive u v h k r)

theorem holomorphicTensorMetricWithReference_weight
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (r : HolomorphicMetric.Data.HolomorphicLineMetricData (u + v)) (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    (holomorphicTensorMetricWithReference u v h k r).weight i ⟨x.val, x.property.1⟩ =
      holomorphicTensorMetricLocalWeight u v h k i x := by
  change holomorphicTensorMetricRatio u v h k r x.val * r.weight i ⟨x.val, x.property.1⟩ = _
  rw [holomorphicTensorMetricRatio_onOpen u v h k r i x]
  exact div_mul_cancel₀ _ (ne_of_gt (r.positive i _))

variable [FiniteDimensional ℝ E] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def holomorphicTensorMetric (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v) :
    HolomorphicMetric.Data.HolomorphicLineMetricData (u + v) :=
  holomorphicTensorMetricWithReference u v h k (HolomorphicMetric.Data.holomorphicLineCanonicalMetric (u + v))

theorem holomorphicTensorMetric_weight (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (k : HolomorphicMetric.Data.HolomorphicLineMetricData v)
    (i : M) (x : TensorGaugeTransitions.holomorphicTensorDomain E M u v i) :
    (holomorphicTensorMetric u v h k).weight i ⟨x.val, x.property.1⟩ =
      h.weight i ⟨x.val, x.property.2.1⟩ * k.weight i ⟨x.val, x.property.2.2⟩ /
        Complex.normSq ((TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val x) :=
  holomorphicTensorMetricWithReference_weight u v h k (HolomorphicMetric.Data.holomorphicLineCanonicalMetric (u + v)) i x

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorMetric
