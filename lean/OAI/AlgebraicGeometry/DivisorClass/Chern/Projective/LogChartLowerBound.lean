import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogTransitionBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogCurvatureSupport

/-! # Log Chart Lower Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogChartLowerBound

noncomputable section

/-! Inner semipositivity, the compact transition estimate, and actual vanishing off support give one uniform bound throughout the original chart. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveLogPointPotential_chart_lower_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hηx : η =ᶠ[𝓝 x] fun _ => 1) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
      ∀ z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, ∀ v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      -B * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v ≤
        (Complex.I * Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
          (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z ![v, Complex.I • v]).re := by
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp hηx
  let K := tsupport η \ U
  have hK : IsCompact K := hc.isCompact.diff hUo
  have hKD : K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun _ hz => hs hz.1
  have hxK : x ∉ K := fun hx => hx.2 hxU
  let bound := LogTransitionBound.projectiveLogPointPotential_transition_lower_bound V e he η hη hc hs x m hK hKD hxK
  refine ⟨bound.choose, bound.choose_spec.1, ?_⟩
  intro ε hε hε1 z hz v
  have hmetric : 0 ≤ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz v hv).le
  have hlower : -bound.choose * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr bound.choose_spec.1.le) hmetric
  by_cases hzU : z ∈ U
  · have hone : η =ᶠ[𝓝 z] fun _ => 1 :=
      Filter.Eventually.mono (hUo.mem_nhds hzU) (fun _ hy => hU hy)
    exact hlower.trans (LogPointCurvature.projectiveLogPointPotential_curvature_nonneg V e he η hη hc hs x m ε hε hz hone v)
  · by_cases hzη : z ∈ tsupport η
    · exact bound.choose_spec.2 ε hε hε1 z ⟨hzη, hzU⟩ v
    · rw [LogCurvatureSupport.projectiveLogPointPotential_curvature_zero_off_cutoff V e he η hη hc hs x m ε hε hz hzη]
      change -bound.choose * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v ≤ (Complex.I * (0 : ℂ)).re
      simpa only [mul_zero, Complex.zero_re] using hlower

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogChartLowerBound
