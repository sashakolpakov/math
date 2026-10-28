import OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption
import OAI.Analysis.HodgeTheory.Decomposition.ChartTestDifferentials
import OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner

/-! # Smooth Chart Forcing -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothChartForcing.Constructions

noncomputable section

section

/-! The L² adjoint forcing has the correct actual chart-test pairings;
for tests on which the cutoff is one, the lift is the unmodified test form. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projectiveSchwartzTestLocalized_eq_lift
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hcs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hgc : ∀ z ∈ tsupport c, g z = 1) :
    ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c = ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hcs := by
  apply ChartCoefficientFaithful.Constructions.projectiveChartTestLift_unique V e he n c hc hcs
  · exact ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs c
  · intro z
    rw [ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients]
    by_cases hz : z ∈ tsupport c
    · rw [hgc z hz, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hz, smul_zero]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveChartForcingL2_pair_real
    (f : Form.Constructions.ProjectiveL2Forms V n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    inner ℝ (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n g hg hs f) (c.toLp 2 volume) =
      (inner ℂ f (Form.Constructions.smoothToProjectiveL2 V n
        (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c))).re := by
  rw [CompatibleRealInner.Constructions.compatible_real_inner, ChartTestAbsorption.Constructions.projectiveChartForcingL2_pair]

theorem projectiveChartForcingL2_test_pair
    (f : Form.Constructions.ProjectiveL2Forms V n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hcs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hgc : ∀ z ∈ tsupport c, g z = 1) :
    inner ℝ (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n g hg hs f) (c.toLp 2 volume) =
      (inner ℂ f (Form.Constructions.smoothToProjectiveL2 V n (ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hcs))).re := by
  rw [projectiveChartForcingL2_pair_real,
    projectiveSchwartzTestLocalized_eq_lift V e he n g hg hs c hc hcs hgc]

theorem projectiveChartForcingL2_smooth_pair
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    inner ℝ (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n g hg hs (Form.Constructions.smoothToProjectiveL2 V n a)) (c.toLp 2 volume) =
      ∫ z, inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
        (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) (g z • c z) := by
  rw [projectiveChartForcingL2_pair_real, Form.Constructions.smoothToProjectiveL2_inner]
  change (Form.Constructions.projectiveL2Pair V n a (ChartTestForms.Constructions.projectiveChartTestLift V e he n (SchwartzMap.smulLeftCLM _ g c)
    (ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hg c) ((ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c).trans hs))).re = _
  rw [ChartTestDifferentials.Constructions.projectiveChartTestLift_pair]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => congrArg
    (fun w => inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
      (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) w)
    (SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth c z))

end

section

/-! Smooth global forcing has an actual smooth compactly supported local
representative, equal to the Hilbert-adjoint forcing already constructed. -/

open _root_.MeasureTheory
open scoped SchwartzMap _root_.Topology ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)

def projectiveSmoothChartForcingFunction (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  (g z).re • AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)

include he hs in
theorem projectiveSmoothChartForcingFunction_smooth :
    ContDiff ℝ ∞ (projectiveSmoothChartForcingFunction V e n g a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · exact (Complex.reCLM.contDiff.comp (g.smooth ⊤)).contDiffAt.smul
      ((((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).clm_apply
        (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he n a)).contDiffAt
          ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)))
  · have hzero : (g : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hs h))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hzero] with x hx
    change g x = 0 at hx
    change (g x).re • AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n x
      (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val x) = 0
    rw [hx, Complex.zero_re, zero_smul]

include hg in
theorem projectiveSmoothChartForcingFunction_compact :
    HasCompactSupport (projectiveSmoothChartForcingFunction V e n g a) := by
  apply hg.mono
  intro x hx hzero
  apply hx
  change (g x).re • AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n x
    (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val x) = 0
  rw [hzero, Complex.zero_re, zero_smul]

def projectiveSmoothChartForcing :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :=
  (projectiveSmoothChartForcingFunction_compact V e n g hg a).toSchwartzMap
    (projectiveSmoothChartForcingFunction_smooth V e he n g hs a)

theorem projectiveSmoothChartForcing_apply (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveSmoothChartForcing V e he n g hg hs a z =
      (g z).re • AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z) := rfl

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveChartForcingL2_smooth
    (hreal : ∀ z, g z = Complex.ofReal (g z).re) :
    ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n g hg hs (Form.Constructions.smoothToProjectiveL2 V n a) =
      (projectiveSmoothChartForcing V e he n g hg hs a).toLp 2 volume := by
  apply ext_inner_right ℝ
  intro v
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ
      (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (by norm_num)
  refine hdense.induction_on v
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)) ?_
  intro c
  change inner ℝ (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n g hg hs (Form.Constructions.smoothToProjectiveL2 V n a))
      (c.toLp 2 volume) = _
  rw [projectiveChartForcingL2_smooth_pair, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(projectiveSmoothChartForcing V e he n g hg hs a).coeFn_toLp 2 volume,
    c.coeFn_toLp 2 volume] with z hF hc
  change inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
    (EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z)) (g z • c z) =
    inner ℝ ((projectiveSmoothChartForcing V e he n g hg hs a).toLp 2 volume z)
      (c.toLp 2 volume z)
  rw [hF, hc, projectiveSmoothChartForcing_apply]
  have hsmul : g z • c z = (g z).re • c z :=
    (congrArg (fun r : ℂ => r • c z) (hreal z)).trans (algebraMap_smul ℂ (g z).re (c z))
  rw [hsmul, real_inner_smul_right, real_inner_smul_left]

end

/-! Genuine smooth manifold forcing has every natural Sobolev order
under the actual local forcing operator. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

theorem projectiveChartForcingL2_smooth_memSobolev (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
    (τ : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hτc : HasCompactSupport τ)
    (hτs : tsupport τ ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hτreal : ∀ x, τ x = Complex.ofReal (τ x).re)
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) (s : ℕ) :
    MemSobolev (s : ℝ) 2
      (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he n τ hτc hτs (Form.Constructions.smoothToProjectiveL2 V n f) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) := by
  rw [projectiveChartForcingL2_smooth V e he n τ hτc hτs f hτreal,
    Lp.toTemperedDistribution_toLp_eq]
  exact (projectiveSmoothChartForcing V e he n τ hτc hτs f).memSobolev

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothChartForcing.Constructions
