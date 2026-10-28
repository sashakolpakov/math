import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms

/-! # Two Form Chart Coefficients -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormChartCoefficients.CM.Construction

noncomputable section

/-! Smooth mixed coefficients of genuine projective two-forms, with
the chartwise differential symmetry imposed by closedness and type. -/

open scoped ContDiff _root_.Topology

def varietyTwoFormMixedCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (i j : Fin V.complexDimension) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
    (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V i) (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)

theorem varietyTwoFormMixedCoefficient_eq_euclidean (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (i j : Fin V.complexDimension) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    varietyTwoFormMixedCoefficient V e a i j z =
      MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.val z)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  rw [Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm, MixedTwoChartMetric.CM.Construction.mixedTwoCoefficient_pullback]
  rfl

theorem mixedTwoCoefficient_contDiffOn {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} (f : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : ContDiffOn ℝ ∞ f U) (u v : E) :
    ContDiffOn ℝ ∞ (fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) u v) U := by
  have h (w : Fin 2 → E) : ContDiffOn ℝ ∞ (fun y => f y w) U :=
    (ContinuousAlternatingMap.apply ℝ E ℂ w).contDiff.comp_contDiffOn hf
  have hs : ContDiffOn ℝ ∞ (fun y => f y ![u, v] + f y ![Complex.I • u, Complex.I • v] -
      Complex.I * f y ![u, Complex.I • v] + Complex.I * f y ![Complex.I • u, v]) U :=
    (((h ![u, v]).add (h ![Complex.I • u, Complex.I • v])).sub
    (contDiffOn_const.mul (h ![u, Complex.I • v]))).add
      (contDiffOn_const.mul (h ![Complex.I • u, v]))
  have hr : ContDiffOn ℝ ∞ (fun y => (1 / 4 : ℂ) *
      (f y ![u, v] + f y ![Complex.I • u, Complex.I • v] -
        Complex.I * f y ![u, Complex.I • v] + Complex.I * f y ![Complex.I • u, v])) U :=
    contDiffOn_const.mul hs
  simpa only [MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply, KahlerDifferential.CM.Construction.twoFormBilinear_apply] using hr

theorem varietyTwoFormMixedCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (i j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyTwoFormMixedCoefficient V e a i j)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  exact (mixedTwoCoefficient_contDiffOn _ (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 a) _ _).congr
    (fun z _ => varietyTwoFormMixedCoefficient_eq_euclidean V e a i j z)

theorem variety_closed_type11_holomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j k : Fin V.complexDimension) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (varietyTwoFormMixedCoefficient V e a j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (varietyTwoFormMixedCoefficient V e a j i) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) := by
  let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.val
  have hf : DifferentiableAt ℝ f z :=
    ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 a).contDiffAt
      ((EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have ht : ∀ᶠ y in 𝓝 z, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 1 (f y) := by
    filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact MixedTwoChartMetric.CM.Construction.type11_pullback _ (ha e he _ hy) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap
  have hd : extDeriv f z = 0 := by
    rw [← Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_d V e he 2 a z hz, hc]
    ext v
    rfl
  have hcoeff (r s : Fin V.complexDimension) : varietyTwoFormMixedCoefficient V e a r s =
      fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ r)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ s) :=
    funext (varietyTwoFormMixedCoefficient_eq_euclidean V e a r s)
  rw [hcoeff, hcoeff]
  exact ClosedTwo.CM.Construction.closed_type11_holomorphic_derivative f hf ht hd _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormChartCoefficients.CM.Construction
