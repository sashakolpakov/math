import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogParameterSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogPointCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.MetricDomination

/-! # Log Transition Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogTransitionBound

noncomputable section

/-! The actual logarithmic cutoff curvature has one original projective metric lower bound on every compact transition region, uniformly down to regularization parameter zero. -/

open Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveLogPointPotential_transition_lower_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (m : ℕ)
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKD : K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hx : x ∉ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 → ∀ z ∈ K, ∀ v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      -B * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v ≤
        (Complex.I * Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
          (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z ![v, Complex.I • v]).re := by
  let F := fun p : ℝ × ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => extDeriv
    (fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
      (fderiv ℝ (η * RegularizedLogWeight.regularizedNegativeLog x m p.1) y)) p.2
  have hF : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ K) := RegularizedLogParameterSmooth.regularizedLogCutoff_curvature_continuous x m η hη hx
  have hB : ContinuousOn (fun p => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm (Complex.I • F p)) (Icc (0 : ℝ) 1 ×ˢ K) :=
    ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_smooth.continuous.comp_continuousOn (hF.const_smul Complex.I)
  have hQ : ContinuousOn (fun p : ℝ × ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e p.2)
      (Icc (0 : ℝ) 1 ×ˢ K) :=
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).continuousOn.comp continuous_snd.continuousOn (fun _ hp => hKD hp.2)
  obtain ⟨N, hN, hbound⟩ := Compact.MetricDomination.compact_bilinear_positive_after_nat_multiple
    (fun p => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm (Complex.I • F p)) (fun p => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e p.2)
    (isCompact_Icc.prod hK) hB hQ (fun p hp v hv => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hKD hp.2) v hv)
  refine ⟨(N : ℝ), by exact_mod_cast hN, ?_⟩
  intro ε hε hε1 z hz v
  by_cases hv : v = 0
  · subst v
    simp only [map_zero, smul_zero]
    rw [← ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply]
    simp
  · have hb := hbound N le_rfl (ε, z) ⟨⟨hε.le, hε1⟩, hz⟩ v hv
    rw [ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.metricFromTwoForm_apply] at hb
    change 0 < (Complex.I * F (ε, z) ![v, Complex.I • v]).re + (N : ℝ) * ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v v at hb
    have hcoord := LogPointCurvature.projectiveLogPointPotential_curvature_full V e he η hη hc hs x m ε hε (hKD hz)
    change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2
      (ScalarPotential.globalScalarCurvature (LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).val z = F (ε, z) at hcoord
    rw [hcoord]
    linarith only [hb]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogTransitionBound
