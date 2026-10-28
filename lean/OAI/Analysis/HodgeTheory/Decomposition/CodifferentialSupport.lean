import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality
import OAI.Analysis.HodgeTheory.Decomposition.LocalCoefficientOperators
import OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates

/-! # Codifferential Support -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport.Constructions

noncomputable section

/-! The actual global codifferential is local and preserves support. -/

open scoped _root_.Manifold _root_.Topology ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem euclideanChartCoefficients_zero_iff_at
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n a (MeasureVolume.Constructions.chartCoordinateForward V e x) = 0 ↔ a x = 0 := by
  constructor
  · intro h
    rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic] at h
    change SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n
      (a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)))) = 0 at h
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    have hc : a.inChart e (e x) = 0 := (SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n).map_eq_zero_iff.mp h
    ext v
    have hv := congrArg (fun f : DifferentialForms.Manifold.Basic.FormValue V.analyticModel n =>
      f (fun i => DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx (v i))) hc
    rw [a.inChart_at e he x hx] at hv
    change a x (fun i => (DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx).symm (DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x hx (v i))) = 0 at hv
    change a x v = 0
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hv
  · intro h
    apply SupportedCoordinates.Constructions.euclideanChartCoefficients_zero_of_value_zero V e n a
    rwa [MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveCodifferential_zero_off_closed (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {K : Set V.analyticSpace} (hK : IsClosed K) (ha : ∀ x, x ∉ K → a x = 0)
    {x : V.analyticSpace} (hx : x ∉ K) : AdjointAlgebra.Constructions.projectiveCodifferential V n a x = 0 := by
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
  have hxe : x ∈ e.source := mem_chart_source _ _
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hxe
  have hix : MeasureVolume.Constructions.chartCoordinateInverse V e z = x := MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hxe
  have hnear : ∀ᶠ y in 𝓝 z, MeasureVolume.Constructions.chartCoordinateInverse V e y ∉ K :=
    ((MeasureVolume.Constructions.chartCoordinateInverse_continuousOn V e).continuousAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).eventually
        (by rw [hix]; exact hK.isOpen_compl.mem_nhds hx)
  have hzero : EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) a.val =ᶠ[𝓝 z] 0 := by
    filter_upwards [hnear] with y hy
    exact SupportedCoordinates.Constructions.euclideanChartCoefficients_zero_of_value_zero V e (n + 1) a.val y (ha _ hy)
  apply (euclideanChartCoefficients_zero_iff_at V e he n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val x hxe).mp
  rw [AdjointLocality.Constructions.projectiveCodifferential_coefficients V n e he a z hz,
    LocalCoefficientOperators.Constructions.projectiveLocalAdjointCoefficients_operator_formula V e n he _
      (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he (n + 1) a) z hz,
    hzero.fderiv_eq, hzero.eq_of_nhds]
  simp

end

end OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport.Constructions
