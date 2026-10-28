import OAI.Analysis.HodgeTheory.Decomposition.CutoffCommutator
import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality
import OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity

/-! # Real Multiplier -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RealMultiplier.Constructions

noncomputable section

/-! Real smooth cutoffs on genuine manifold forms and their chart expressions. -/

open scoped _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveRealFunction_complex_smooth (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.contDiff.contMDiff.comp hf

theorem projectiveRealFunction_complex_tsupport (f : V.analyticSpace → ℝ) :
    tsupport (fun x => (f x : ℂ)) = tsupport f := by
  apply congrArg closure
  ext x
  simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]

def projectiveRealMultiplier (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ]
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (fun x => (f x : ℂ))
    (Complex.ofRealCLM.contDiff.contMDiff.comp hf)

theorem projectiveRealMultiplier_zero_off_support (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {x : V.analyticSpace} (hx : x ∉ tsupport f) : projectiveRealMultiplier V n f hf a x = 0 := by
  change (f x : ℂ) • a x = 0
  rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]
  exact zero_smul ℂ (a x)

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

theorem projectiveRealMultiplier_coefficients (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanForms.Constructions.euclideanChartCoefficients V e n (projectiveRealMultiplier V n f hf a).val z =
      f (MeasureVolume.Constructions.chartCoordinateInverse V e z) • EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z := by
  rw [EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic, EuclideanForms.Constructions.euclideanChartCoefficients_eq_analytic]
  change SymbolDifferential.Constructions.exteriorCoordinateEquiv (AdjointCoefficients.Constructions.projectiveReferenceBasis V) n
    ((DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (fun x => (f x : ℂ)) a.val).inChart e (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  simp only [map_smul]
  exact algebraMap_smul ℂ (f (MeasureVolume.Constructions.chartCoordinateInverse V e z)) _

include he

theorem projectiveRealFunction_chart_smooth (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (fun z => f (MeasureVolume.Constructions.chartCoordinateInverse V e z)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have heSmooth : ContMDiffOn 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, V.analyticModel) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  have hfChart : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
    (hf.comp_contMDiffOn heSmooth).contDiffOn
  exact hfChart.comp ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)

end

end OAI.Analysis.HodgeTheory.Decomposition.RealMultiplier.Constructions
