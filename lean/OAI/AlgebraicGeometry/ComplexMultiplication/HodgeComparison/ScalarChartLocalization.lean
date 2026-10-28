import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs

/-! # Scalar Chart Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization.CM.Construction

noncomputable section

/-! A compact cutoff of an actual global smooth scalar function gives a
Schwartz function in each Euclidean chart, with the actual differential. -/

open _root_.MeasureTheory Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology

def varietyScalarChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm ∘ EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V

theorem varietyScalarChart_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    ContDiffOn ℝ ∞ (varietyScalarChart V e f) (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
  intro z hz
  exact ((HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart f e he hz).comp z
    (((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt)).contDiffWithinAt

theorem varietyScalarChart_differential (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    {x : V.analyticSpace} (hx : x ∈ e.source) (i : ι) :
    GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x i =
      fderiv ℝ (varietyScalarChart V e f) ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) (b i) := by
  have hd := ((HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart f e he (e.map_source hx)).differentiableAt (by simp)).hasFDerivAt
  have hL : HasFDerivAt (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V)
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ)
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) :=
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt
  have hd' : HasFDerivAt (varietyScalarChart V e f)
      ((fderiv ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm) (e x)).comp
        ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ))
      ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) := by
    have hdL : HasFDerivAt (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm)
        (fderiv ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm) (e x))
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x))) := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hd
    exact hdL.comp _ hL
  rw [hd'.fderiv]
  change ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f).val.inChart e (e x))
    (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (b i)) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart f e he (e.map_source hx), HolomorphicPrimitive.CM.Construction.zeroFormScalar_reconstruct,
    extDeriv_constOfIsEmpty]
  rfl

theorem varietyScalarChart_cutoff_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    ContDiff ℝ ∞ (fun z => g z * varietyScalarChart V e f z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e
  · exact (g.smooth ⊤).contDiffAt.mul ((varietyScalarChart_smooth V e he f).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz))
  · have hzero : (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hg h))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

def varietyScalarChartCutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ) :=
  (hgc.mul_right (f' := varietyScalarChart V e f)).toSchwartzMap
    (varietyScalarChart_cutoff_smooth V e he g hg f)

theorem varietyScalarChartCutoff_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    varietyScalarChartCutoff V e he g hgc hg f z = g z * varietyScalarChart V e f z := rfl

theorem varietyScalarChartCutoff_support (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietyScalarChartCutoff V e he g hgc hg f ∈ SobolevIs.CM.Construction.supportedSchwartzSubmodule (tsupport g) := by
  intro z hz
  rw [varietyScalarChartCutoff_apply, image_eq_zero_of_notMem_tsupport hz, zero_mul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ScalarChartLocalization.CM.Construction
