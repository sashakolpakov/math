import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms
import OAI.Analysis.DifferentialForms.Manifold.LocalDerivative

/-! # Supported Coordinates -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions

noncomputable section

/-! Extension by zero of genuine chart coefficients for forms whose support
is contained in a compact subset of the chart source. -/

open scoped ContDiff _root_.Manifold _root_.Topology
open Set

section Extension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_of_support_in_closed (f : E → F) {K U : Set E}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hs : Function.support f ⊆ K) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hxt : x ∉ tsupport f := fun ht => hx (hKU ((closure_minimal hs hK) ht))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hxt)

end Extension

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem euclideanChartCoefficients_zero_of_value_zero
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (ha : a (MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0) : EuclideanForms.Constructions.euclideanChartCoefficients V e n a z = 0 := by
  have hchart : a.inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) = 0 := by
    unfold DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    change (a (MeasureVolume.Constructions.chartCoordinateInverse V e z)).compContinuousLinearMap _ = 0
    rw [ha]
    ext v
    rfl
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic V e n a z, hchart, map_zero]

/-- Chart coefficients with value zero outside the actual chart domain. -/
def supportedEuclideanCoefficients (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _).indicator (EuclideanForms.Constructions.euclideanChartCoefficients V e n a)

theorem supportedEuclideanCoefficients_eq
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    supportedEuclideanCoefficients V e n a z = EuclideanForms.Constructions.euclideanChartCoefficients V e n a z :=
  Set.indicator_of_mem hz _

theorem supportedEuclideanCoefficients_eventuallyEq
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    supportedEuclideanCoefficients V e n a =ᶠ[𝓝 z] EuclideanForms.Constructions.euclideanChartCoefficients V e n a := by
  filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
  exact supportedEuclideanCoefficients_eq V e n a hy

theorem supportedEuclideanCoefficients_support
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (ha : ∀ x, x ∉ K → a x = 0) :
    Function.support (supportedEuclideanCoefficients V e n a) ⊆ MeasureVolume.Constructions.chartCoordinateForward V e '' K := by
  intro z hz
  have hzU : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    by_contra hn
    exact hz (Set.indicator_of_notMem hn _)
  refine ⟨MeasureVolume.Constructions.chartCoordinateInverse V e z, ?_, MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzU⟩
  by_contra hx
  apply hz
  rw [supportedEuclideanCoefficients_eq V e n a hzU]
  exact euclideanChartCoefficients_zero_of_value_zero V e n a z (ha _ hx)

theorem chartCoordinateForward_compact {K : Set V.analyticSpace}
    (hK : IsCompact K) (hKe : K ⊆ e.source) : IsCompact (MeasureVolume.Constructions.chartCoordinateForward V e '' K) :=
  hK.image_of_continuousOn
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn (e.continuousOn.mono hKe))

theorem supportedEuclideanCoefficients_tsupport
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    tsupport (supportedEuclideanCoefficients V e n a) ⊆ MeasureVolume.Constructions.chartCoordinateForward V e '' K :=
  closure_minimal (supportedEuclideanCoefficients_support V e n a ha)
    (chartCoordinateForward_compact V e hK hKe).isClosed

theorem supportedEuclideanCoefficients_compact
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    HasCompactSupport (supportedEuclideanCoefficients V e n a) :=
  (chartCoordinateForward_compact V e hK hKe).of_isClosed_subset (isClosed_tsupport _)
    (supportedEuclideanCoefficients_tsupport V e n a hK hKe ha)

theorem supportedEuclideanCoefficients_tsupport_domain
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    tsupport (supportedEuclideanCoefficients V e n a) ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := supportedEuclideanCoefficients_tsupport V e n a hK hKe ha hz
  exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)

include he

theorem supportedEuclideanCoefficients_smooth
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (hK : IsCompact K) (hKe : K ⊆ e.source) (ha : ∀ x, x ∉ K → a x = 0) :
    ContDiff ℝ ∞ (supportedEuclideanCoefficients V e n a.val) := by
  apply smooth_of_support_in_closed _ (chartCoordinateForward_compact V e hK hKe).isClosed
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
  · rintro z ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  · exact supportedEuclideanCoefficients_support V e n a.val ha
  · exact (EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he n a).congr
      (fun z hz => supportedEuclideanCoefficients_eq V e n a.val hz)

/-- The zero extension has the same actual differential at every point of its chart. -/
theorem supportedEuclideanCoefficients_d
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val z =
      LocalAdjoint.Constructions.firstOrderCoordinateOperator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
        (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n) (supportedEuclideanCoefficients V e n a.val) z := by
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_d V e he n a z hz]
  unfold LocalAdjoint.Constructions.firstOrderCoordinateOperator
  rw [(supportedEuclideanCoefficients_eventuallyEq V e n a.val hz).fderiv_eq]

omit he in
/-- Exterior differentiation does not enlarge support, by its proved locality. -/
theorem manifold_d_zero_off_closed
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) {K : Set V.analyticSpace}
    (hK : IsClosed K) (ha : ∀ x, x ∉ K → a x = 0) {x : V.analyticSpace} (hx : x ∉ K) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x = 0 := by
  have h := DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_congr_on a.val
    (0 : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) hK.isOpen_compl ha hx
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x =
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (0 : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) x at h
  simpa only [map_zero, DifferentialForms.Manifold.Algebra.SmoothManifoldForm.zero_apply] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions
