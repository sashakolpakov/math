import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential

/-! # Chart Test Absorption -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions

noncomputable section

section

/-! The actual chart test extension is bounded in L² and therefore extends
to Euclidean L² coefficients. Its Hilbert adjoint gives local forcing. -/

open scoped SchwartzMap
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem projectiveSchwartzTestLocalized_Lp
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    CoordinateLp.Constructions.supportedCoordinatesLp V e he n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hs)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
      (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c)
      (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero V e he n g hg hs c) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (c.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hs)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
    (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c)
    (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero V e he n g hg hs c)).coeFn_toLp,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (c.toLp 2 volume), c.coeFn_toLp 2 volume] with z hleft hright hc
  exact hleft.trans ((ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients V e he n g hg hs c z).trans
    ((congrArg (fun v => g z • v) hc).symm.trans hright.symm))

def projectiveSchwartzTestL2 :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) →ₗ[ℂ]
      Form.Constructions.ProjectiveL2Forms V n :=
  (Form.Constructions.smoothToProjectiveL2 V n).comp (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLinear V e he n g hg hs)

theorem projectiveSchwartzTestL2_bound :
    ∃ B : ℝ, ∀ c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
        SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n),
      ‖projectiveSchwartzTestL2 V e he n g hg hs c‖ ≤ B * ‖c.toLp 2 volume‖ := by
  obtain ⟨C, hC, hbound⟩ := CoordinateLp.Constructions.projective_supported_coordinate_upper V e he n
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_isCompact V e hg hs)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs)
  refine ⟨Real.sqrt C * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply
    (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) g‖, fun c => ?_⟩
  have hsq := hbound (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c)
    (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero V e he n g hg hs c)
  rw [projectiveSchwartzTestLocalized_Lp] at hsq
  have hroot : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  have hnorm : ‖projectiveSchwartzTestL2 V e he n g hg hs c‖ ≤
      Real.sqrt C * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (c.toLp 2 volume)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hroot (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hC.le]
    exact hsq
  exact hnorm.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g).le_opNorm (c.toLp 2 volume)) hroot)

def projectiveChartTestL2 :
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℂ] Form.Constructions.ProjectiveL2Forms V n :=
  (projectiveSchwartzTestL2 V e he n g hg hs).extendOfNorm
    (SchwartzMap.toLpCLM ℂ _ 2 volume).toLinearMap

theorem projectiveChartTestL2_on_schwartz
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    projectiveChartTestL2 V e he n g hg hs (c.toLp 2 volume) =
      Form.Constructions.smoothToProjectiveL2 V n (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℂ
      (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) := by
    exact SchwartzMap.denseRange_toLpCLM (E := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
      (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
      (μ := volume) (p := 2) (by norm_num)
  exact LinearMap.extendOfNorm_eq hdense
    (projectiveSchwartzTestL2_bound V e he n g hg hs) c

def projectiveChartForcingL2 : Form.Constructions.ProjectiveL2Forms V n →L[ℂ]
    Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (projectiveChartTestL2 V e he n g hg hs).adjoint

theorem projectiveChartForcingL2_pair
    (f : Form.Constructions.ProjectiveL2Forms V n)
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    inner ℂ (projectiveChartForcingL2 V e he n g hg hs f) (c.toLp 2 volume) =
      inner ℂ f (Form.Constructions.smoothToProjectiveL2 V n
        (ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hs c)) := by
  rw [projectiveChartForcingL2, ContinuousLinearMap.adjoint_inner_left,
    projectiveChartTestL2_on_schwartz]

end

/-! A chart reconstruction cutoff absorbs any scalar multiplier equal to
one on its support, both on Schwartz tests and on genuine L² fields. -/

open _root_.MeasureTheory
open scoped SchwartzMap
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

theorem vectorSchwartzMultiply_toLp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : 𝓢(E, ℂ)) (c : 𝓢(E, F)) :
    (SchwartzMap.smulLeftCLM F g c).toLp 2 volume = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (c.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.smulLeftCLM F g c).coeFn_toLp 2 volume,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (c.toLp 2 volume), c.coeFn_toLp 2 volume] with x hleft hright hc
  rw [hleft, hright, hc, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (β : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hβc : HasCompactSupport β)
  (hβs : tsupport β ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : ∀ x ∈ tsupport β, g x = 1)

include hg in
theorem projectiveSchwartzTestLocalized_absorb
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n β hβc hβs (SchwartzMap.smulLeftCLM _ g c) =
      ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n β hβc hβs c := by
  apply Subtype.ext
  apply ChartCoefficientFaithful.Constructions.supportedCoefficients_faithful V e he n
  · exact ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero_off_source V e he n β hβc hβs _
  · exact ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero_off_source V e he n β hβc hβs _
  · intro x
    rw [ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients, ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients,
      SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    by_cases hx : x ∈ tsupport β
    · rw [hg x hx, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, zero_smul]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

include hg in
theorem projectiveChartTestL2_absorb
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    projectiveChartTestL2 V e he n β hβc hβs (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u) =
      projectiveChartTestL2 V e he n β hβc hβs u := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℂ
      (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (by norm_num)
  have hclosed : IsClosed {v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) |
      projectiveChartTestL2 V e he n β hβc hβs (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g v) =
        projectiveChartTestL2 V e he n β hβc hβs v} :=
    isClosed_eq ((projectiveChartTestL2 V e he n β hβc hβs).continuous.comp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g).continuous)
      (projectiveChartTestL2 V e he n β hβc hβs).continuous
  refine hdense.induction_on u hclosed (fun c => ?_)
  change projectiveChartTestL2 V e he n β hβc hβs (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (c.toLp 2 volume)) =
    projectiveChartTestL2 V e he n β hβc hβs (c.toLp 2 volume)
  rw [← vectorSchwartzMultiply_toLp, projectiveChartTestL2_on_schwartz, projectiveChartTestL2_on_schwartz,
    projectiveSchwartzTestLocalized_absorb V e he n β hβc hβs g hg c]

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions
