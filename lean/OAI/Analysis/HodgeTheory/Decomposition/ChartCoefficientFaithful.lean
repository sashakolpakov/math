import OAI.Analysis.HodgeTheory.Decomposition.ChartTestForms
import OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity

/-! # Chart Coefficient Faithful -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions

noncomputable section

section

/-! Actual tangent-covector fields supported in one chart are determined
by their Euclidean coefficients; the constructed chart test lift is unique. -/

open scoped SchwartzMap

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he in
theorem euclideanChartCoefficients_eq_at
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) (hx : x ∈ e.source)
    (h : EuclideanForms.Constructions.euclideanChartCoefficients V e n a (MeasureVolume.Constructions.chartCoordinateForward V e x) =
      EuclideanForms.Constructions.euclideanChartCoefficients V e n b (MeasureVolume.Constructions.chartCoordinateForward V e x)) : a x = b x := by
  have hsub : EuclideanForms.Constructions.euclideanChartCoefficients V e n (a - b) (MeasureVolume.Constructions.chartCoordinateForward V e x) = 0 := by
    have heq := congrFun ((CoefficientLinearity.Constructions.euclideanChartCoefficientLinear V e n).map_sub a b) (MeasureVolume.Constructions.chartCoordinateForward V e x)
    change EuclideanForms.Constructions.euclideanChartCoefficients V e n (a - b) (MeasureVolume.Constructions.chartCoordinateForward V e x) =
      EuclideanForms.Constructions.euclideanChartCoefficients V e n a (MeasureVolume.Constructions.chartCoordinateForward V e x) -
      EuclideanForms.Constructions.euclideanChartCoefficients V e n b (MeasureVolume.Constructions.chartCoordinateForward V e x) at heq
    rw [heq, h, sub_self]
  have hz := (CodifferentialSupport.Constructions.euclideanChartCoefficients_zero_iff_at V e he n (a - b) x hx).mp hsub
  exact sub_eq_zero.mp hz

include he in
theorem supportedCoefficients_faithful
    (a b : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ x, x ∉ e.source → a x = 0) (hb : ∀ x, x ∉ e.source → b x = 0)
    (h : ∀ z, SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a z = SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n b z) : a = b := by
  funext x
  by_cases hx : x ∈ e.source
  · apply euclideanChartCoefficients_eq_at V e he n a b x hx
    have heq := h (MeasureVolume.Constructions.chartCoordinateForward V e x)
    rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a (MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx),
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n b (MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx)] at heq
    exact heq
  · rw [ha x hx, hb x hx]

theorem projectiveChartTestLift_unique
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : HasCompactSupport c) (hs : tsupport c ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ x, x ∉ e.source → a x = 0)
    (hcoeff : ∀ z, SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z = c z) :
    a = ChartTestForms.Constructions.projectiveChartTestLift V e he n c hc hs := by
  apply Subtype.ext
  apply supportedCoefficients_faithful V e he n a.val _ ha
  · intro x hx
    exact ChartTestForms.Constructions.projectiveChartTestLift_zero V e he n c hc hs x
      (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs h))
  · intro z
    rw [hcoeff, ChartTestForms.Constructions.projectiveChartTestLift_coefficients]

end

/-! A fixed chart cutoff gives a genuine complex-linear extension of
arbitrary Euclidean Schwartz form coefficients to global smooth forms. -/

open scoped SchwartzMap

section Support
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem schwartz_cutoff_tsupport (g : 𝓢(E, ℂ)) (c : 𝓢(E, F)) :
    tsupport (SchwartzMap.smulLeftCLM F g c) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  by_contra h
  apply hx
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    image_eq_zero_of_notMem_tsupport h, zero_smul]

theorem schwartz_cutoff_compact (g : 𝓢(E, ℂ)) (hg : HasCompactSupport g) (c : 𝓢(E, F)) :
    HasCompactSupport (SchwartzMap.smulLeftCLM F g c) :=
  hg.of_isClosed_subset (isClosed_tsupport _) (schwartz_cutoff_tsupport g c)

end Support

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

def projectiveSchwartzTestLocalized
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  ChartTestForms.Constructions.projectiveChartTestLift V e he n (SchwartzMap.smulLeftCLM _ g c)
    (schwartz_cutoff_compact g hg c) ((schwartz_cutoff_tsupport g c).trans hs)

theorem projectiveSchwartzTestLocalized_coefficients
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (projectiveSchwartzTestLocalized V e he n g hg hs c).val z =
      g z • c z := by
  rw [projectiveSchwartzTestLocalized, ChartTestForms.Constructions.projectiveChartTestLift_coefficients,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]

theorem projectiveSchwartzTestLocalized_zero
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (x : V.analyticSpace) (hx : x ∉ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) :
    projectiveSchwartzTestLocalized V e he n g hg hs c x = 0 := by
  apply ChartTestForms.Constructions.projectiveChartTestLift_zero
  intro h
  apply hx
  rcases h with ⟨z, hz, rfl⟩
  exact ⟨z, schwartz_cutoff_tsupport g c hz, rfl⟩

theorem projectiveSchwartzTestLocalized_zero_off_source
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (x : V.analyticSpace) (hx : x ∉ e.source) :
    projectiveSchwartzTestLocalized V e he n g hg hs c x = 0 :=
  projectiveSchwartzTestLocalized_zero V e he n g hg hs c x
    (fun h => hx (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hs h))

def projectiveSchwartzTestLinear :
    𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n where
  toFun := projectiveSchwartzTestLocalized V e he n g hg hs
  map_add' c d := by
    apply Subtype.ext
    apply supportedCoefficients_faithful V e he n
    · exact projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs (c + d)
    · intro x hx
      change projectiveSchwartzTestLocalized V e he n g hg hs c x +
        projectiveSchwartzTestLocalized V e he n g hg hs d x = 0
      rw [projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs c x hx,
        projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs d x hx, add_zero]
    · intro z
      have hadd := congrFun ((CoefficientLinearity.Constructions.supportedCoefficientLinear V e n).map_add
        (projectiveSchwartzTestLocalized V e he n g hg hs c).val
        (projectiveSchwartzTestLocalized V e he n g hg hs d).val) z
      change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (projectiveSchwartzTestLocalized V e he n g hg hs c +
          projectiveSchwartzTestLocalized V e he n g hg hs d).val z =
        SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
          (projectiveSchwartzTestLocalized V e he n g hg hs c).val z +
        SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
          (projectiveSchwartzTestLocalized V e he n g hg hs d).val z at hadd
      change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (projectiveSchwartzTestLocalized V e he n g hg hs (c + d)).val z = _
      rw [projectiveSchwartzTestLocalized_coefficients, hadd,
        projectiveSchwartzTestLocalized_coefficients, projectiveSchwartzTestLocalized_coefficients]
      exact smul_add _ _ _
  map_smul' r c := by
    simp only [RingHom.id_apply]
    apply Subtype.ext
    apply supportedCoefficients_faithful V e he n
    · exact projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs (r • c)
    · intro x hx
      change r • projectiveSchwartzTestLocalized V e he n g hg hs c x = 0
      rw [projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hs c x hx]
      ext v
      simp
    · intro z
      have hsmul := congrFun ((CoefficientLinearity.Constructions.supportedCoefficientLinear V e n).map_smul r
        (projectiveSchwartzTestLocalized V e he n g hg hs c).val) z
      change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (r • projectiveSchwartzTestLocalized V e he n g hg hs c).val z =
        r • SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
          (projectiveSchwartzTestLocalized V e he n g hg hs c).val z at hsmul
      change SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n
        (projectiveSchwartzTestLocalized V e he n g hg hs (r • c)).val z = _
      rw [projectiveSchwartzTestLocalized_coefficients, hsmul,
        projectiveSchwartzTestLocalized_coefficients]
      change g z • (r • c z) = r • (g z • c z)
      exact smul_comm (g z) r (c z)

end

end OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions
