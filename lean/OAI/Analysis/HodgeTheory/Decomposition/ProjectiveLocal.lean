import OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianBoundary
import OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianLocality
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveKahlerCommutator
import OAI.Analysis.HodgeTheory.Decomposition.LefschetzRotation

/-! # Projective Local -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLocal.Constructions

noncomputable section

section

/-! The actual projective metric determines a local Hodge operator in
every positive degree, commuting with infinitesimal complex rotation. -/

open scoped ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)

def projectiveLefschetzChartOperator (n : ℕ) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n :=
  LefschetzSymbol.Constructions.metricLefschetzContraction n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis

def projectiveLocalHodgeOperator : (n : ℕ) →
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)) →
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)
  | 0 => LocalLaplacianBoundary.Constructions.localLefschetzLaplacianZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (projectiveLefschetzChartOperator V e 0) (projectiveLefschetzChartOperator V e 1)
  | n + 1 => LocalLaplacianBoundary.Constructions.localLefschetzLaplacian n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (projectiveLefschetzChartOperator V e n) (projectiveLefschetzChartOperator V e (n + 1))
        (projectiveLefschetzChartOperator V e (n + 1 + 1))

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)
include he

theorem projectiveLefschetzChartOperator_smooth_apply (n : ℕ)
    (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1 + 1))
    (ha : ContDiffOn ℝ ∞ a (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _)) :
    ContDiffOn ℝ ∞ (fun y => projectiveLefschetzChartOperator V e n y (a y)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  LefschetzConnection.Constructions.metricLefschetzContraction_smoothOn _ n _ a (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he) (fun _ hy => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hy) ha

theorem projectiveLefschetzChartOperator_rotation (n : ℕ) {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (a : DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1 + 1)) :
    projectiveLefschetzChartOperator V e n z (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) a) =
      ComplexRotationDifferentials.Constructions.complexFormRotation n (projectiveLefschetzChartOperator V e n z a) :=
  LefschetzRotation.Constructions.metricLefschetzContraction_rotation _ n _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz) a

theorem projectiveLocalHodgeOperator_rotation (n : ℕ)
    (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1))
    (ha : ContDiffOn ℝ ∞ a (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (projectiveLocalHodgeOperator V e n a z) =
      projectiveLocalHodgeOperator V e n (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (a y)) z := by
  cases n with
  | zero =>
    exact LocalLaplacianBoundary.Constructions.localLefschetzLaplacianZero_rotation (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis _ _
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (projectiveLefschetzChartOperator_smooth_apply V e he 0)
      (fun _ hy => projectiveLefschetzChartOperator_rotation V e he 0 hy)
      (fun _ hy => projectiveLefschetzChartOperator_rotation V e he 1 hy) a ha hz
  | succ n =>
    exact LocalLaplacianBoundary.Constructions.localLefschetzLaplacian_rotation (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n _ _ _
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (projectiveLefschetzChartOperator_smooth_apply V e he n)
      (projectiveLefschetzChartOperator_smooth_apply V e he (n + 1))
      (fun _ hy => projectiveLefschetzChartOperator_rotation V e he n hy)
      (fun _ hy => projectiveLefschetzChartOperator_rotation V e he (n + 1) hy)
      (fun _ hy => projectiveLefschetzChartOperator_rotation V e he (n + 1 + 1) hy) a ha hz

omit he in
theorem projectiveLocalHodgeOperator_eqOn (n : ℕ)
    {a b : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)}
    (hab : Set.EqOn a b (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)) {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    projectiveLocalHodgeOperator V e n a z = projectiveLocalHodgeOperator V e n b z := by
  cases n with
  | succ n => exact LocalLaplacianLocality.Constructions.localLefschetzLaplacian_eqOn n _ _ _ _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hab hz
  | zero =>
    have heq (y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hy : y ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : a =ᶠ[𝓝 y] b := by
      filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hy] with w hw
      exact hab hw
    have hB : ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (projectiveLefschetzChartOperator V e 0) a =ᶠ[𝓝 z]
        ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (projectiveLefschetzChartOperator V e 0) b := by
      filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
      unfold ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero
      rw [ExteriorConstantBracket.Constructions.twistedExteriorDerivative_congr 1 _ (heq y hy)]
    have hd : extDeriv a =ᶠ[𝓝 z] extDeriv b := by
      filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
      exact LocalLaplacianLocality.Constructions.extDeriv_congr_of_eventuallyEq 1 (heq y hy)
    change extDeriv _ z + ExteriorConstantBracket.Constructions.lefschetzTwistedBracket 0 _ _ _ (extDeriv a) z = extDeriv _ z + _
    rw [LocalLaplacianLocality.Constructions.extDeriv_congr_of_eventuallyEq 0 hB, ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_congr 0 _ _ _ hd]

end

section

/-! A uniform positive-degree local codifferential, identified with the
already constructed global adjoint by the full actual Kähler identity. -/

open scoped _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)

def projectiveLocalCodifferential : (n : ℕ) →
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)) →
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n
  | 0 => ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (projectiveLefschetzChartOperator V e 0)
  | n + 1 => ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (projectiveLefschetzChartOperator V e (n + 1)) (projectiveLefschetzChartOperator V e n)

theorem projectiveLocalHodgeOperator_eq (n : ℕ)
    (a : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveLocalHodgeOperator V e n a z = extDeriv (projectiveLocalCodifferential V e n a) z +
      projectiveLocalCodifferential V e (n + 1) (extDeriv a) z := by
  cases n <;> rfl

theorem projectiveLocalCodifferential_eqOn (n : ℕ)
    {a b : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (n + 1)}
    (hab : Set.EqOn a b (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)) {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    projectiveLocalCodifferential V e n a z = projectiveLocalCodifferential V e n b z := by
  have heq : a =ᶠ[𝓝 z] b := by
    filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact hab hy
  cases n with
  | zero =>
    change projectiveLefschetzChartOperator V e 0 z (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 _ a z) = _
    rw [ExteriorConstantBracket.Constructions.twistedExteriorDerivative_congr 1 _ heq]
    rfl
  | succ n => exact ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_congr n _ _ _ heq

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

include he

theorem projectiveCodifferential_local (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartForm V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val z =
      projectiveLocalCodifferential V e n (EuclideanForms.Constructions.euclideanChartForm V e (n + 1) a.val) z := by
  cases n with
  | zero => exact (ProjectiveKahlerCommutator.Constructions.projectiveKahlerCommutator_zero V e he a hz).symm
  | succ n => exact (ProjectiveKahlerCommutator.Constructions.projectiveKahlerCommutator V e he n a hz).symm

end

/-! The constructed global Hodge Laplacian is exactly the rotation-invariant
local operator of the actual metric in every genuine projective chart. -/

open scoped _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

include he

theorem projectivePositiveLaplacian_chart (n : ℕ)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (AdjointAlgebra.Constructions.projectivePositiveLaplacian V n a).val z =
      projectiveLocalHodgeOperator V e n (EuclideanForms.Constructions.euclideanChartForm V e (n + 1) a.val) z := by
  have hadd : EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (AdjointAlgebra.Constructions.projectivePositiveLaplacian V n a).val z =
      EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AdjointAlgebra.Constructions.projectiveCodifferential V n a)).val z +
        EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).val z := by
    ext v
    rfl
  have hδ : EuclideanForms.Constructions.euclideanChartForm V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val =ᶠ[𝓝 z]
      projectiveLocalCodifferential V e n (EuclideanForms.Constructions.euclideanChartForm V e (n + 1) a.val) := by
    filter_upwards [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact projectiveCodifferential_local V e he n a hy
  have hd : Set.EqOn (EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val)
      (extDeriv (EuclideanForms.Constructions.euclideanChartForm V e (n + 1) a.val)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
    intro y hy
    exact EuclideanForms.Constructions.euclideanChartForm_d V e he (n + 1) a y hy
  rw [hadd, EuclideanForms.Constructions.euclideanChartForm_d V e he n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) z hz,
    LocalLaplacianLocality.Constructions.extDeriv_congr_of_eventuallyEq n hδ, projectiveCodifferential_local V e he (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hz,
    projectiveLocalCodifferential_eqOn V e (n + 1) hd hz, projectiveLocalHodgeOperator_eq]

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLocal.Constructions
