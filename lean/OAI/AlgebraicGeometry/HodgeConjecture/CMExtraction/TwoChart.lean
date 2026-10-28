import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosedTwoDerivatives
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoMetric
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms

/-! # Two Chart -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoChart.Closedness

noncomputable section

/-! Smooth projective (2,0) coefficients and their vanishing antiholomorphic derivatives. -/

open Filter
open scoped ContDiff _root_.Topology

def varietyHolomorphicTwoCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (i j : Fin V.complexDimension) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (a.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))
    (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V i) (ComplexMultiplication.HodgeComparison.HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V j)

theorem varietyHolomorphicTwoCoefficient_eq_euclidean (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (i j : Fin V.complexDimension) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    varietyHolomorphicTwoCoefficient V e a i j z =
      HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.val z)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  rw [Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm, TwoMetric.Closedness.holomorphicTwoCoefficient_pullback]
  rfl

theorem holomorphicTwoCoefficient_contDiffOn {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} (f : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : ContDiffOn ℝ ∞ f U) (u v : E) :
    ContDiffOn ℝ ∞ (fun y => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (f y) u v) U := by
  have h (w : Fin 2 → E) : ContDiffOn ℝ ∞ (fun y => f y w) U :=
    (ContinuousAlternatingMap.apply ℝ E ℂ w).contDiff.comp_contDiffOn hf
  have hs : ContDiffOn ℝ ∞ (fun y => f y ![u, v] - f y ![Complex.I • u, Complex.I • v] -
      Complex.I * f y ![u, Complex.I • v] - Complex.I * f y ![Complex.I • u, v]) U :=
    (((h ![u, v]).sub (h ![Complex.I • u, Complex.I • v])).sub
    (contDiffOn_const.mul (h ![u, Complex.I • v]))).sub
      (contDiffOn_const.mul (h ![Complex.I • u, v]))
  have hr : ContDiffOn ℝ ∞ (fun y => (1 / 4 : ℂ) *
      (f y ![u, v] - f y ![Complex.I • u, Complex.I • v] -
        Complex.I * f y ![u, Complex.I • v] - Complex.I * f y ![Complex.I • u, v])) U :=
    contDiffOn_const.mul hs
  simpa only [HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_apply, ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply] using hr

theorem varietyHolomorphicTwoCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (i j : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyHolomorphicTwoCoefficient V e a i j)
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  exact (holomorphicTwoCoefficient_contDiffOn _
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 a) _ _).congr
    (fun z _ => varietyHolomorphicTwoCoefficient_eq_euclidean V e a i j z)

theorem variety_closed_type20_antiholomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j k : Fin V.complexDimension) :
    ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (varietyHolomorphicTwoCoefficient V e a j k) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) = 0 := by
  let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 a.val
  have hf : DifferentiableAt ℝ f z :=
    ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 a).contDiffAt
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have ht : ∀ᶠ y in 𝓝 z, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 2 0 (f y) := by
    filter_upwards [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    exact TwoMetric.Closedness.type20_pullback _ (ha e he _ hy) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap
  have hd : extDeriv f z = 0 := by
    rw [← Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_d V e he 2 a z hz, hc]
    ext v
    rfl
  have hcoeff : varietyHolomorphicTwoCoefficient V e a j k =
      fun y => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (f y) (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ k) :=
    funext (varietyHolomorphicTwoCoefficient_eq_euclidean V e a j k)
  rw [hcoeff]
  exact ClosedTwoDerivatives.Closedness.closed_type20_coefficient_antiholomorphic_derivative f hf ht hd _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoChart.Closedness
