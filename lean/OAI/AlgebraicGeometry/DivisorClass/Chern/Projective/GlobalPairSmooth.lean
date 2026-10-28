import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence

/-! # Global Pair Smooth -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern

/-! The original global bundle pairing has smooth coordinate density and is integrable against every compact base-chart cutoff. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem Projective.GlobalPairSmooth.projectiveGlobalScalar_smooth (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    ContDiffOn ℝ ∞ (fun z => f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  let g : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) (⊤ : Opens V.analyticSpace) :=
    ⟨fun x => f x.val, hf.comp (contMDiff_subtype_val (I := 𝓘(ℝ, V.analyticModel)))⟩
  have hg : ContDiffOn ℝ ∞ (Projective.BasePartition.projectiveScalarChart V e ⊤ g) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    (Projective.BasePartition.projectiveScalarChart_smooth V e he ⊤ g).mono (fun _ hz => ⟨hz, trivial⟩)
  apply hg.congr
  intro z hz
  rw [Projective.BasePartition.projectiveScalarChart_apply V e ⊤ g ⟨hz, trivial⟩]
  rfl

variable {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_smooth (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ContDiffOn ℝ ∞ (h.projectiveGlobalPair V e n a c) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he)).mul
    (Projective.GlobalPairSmooth.projectiveGlobalScalar_smooth V e he (h.globalFormPair V n a c) (h.globalFormPair_smooth V n a c))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_cutoff_integrable (n : ℕ)
    (a c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (χ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Integrable (fun z => h.projectiveGlobalPair V e n a c z * χ z) :=
  ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test_integrable volume _ χ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (h.projectiveGlobalPair_smooth V e he n a c) hχ hc hs

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth

/-! Original smooth real manifold cutoffs supported in a base chart have compact smooth Euclidean representatives with the exact original values. -/

open Set Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem exists_projectiveRealChartCutoff (ρ : V.analyticSpace → ℝ)
    (hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ) ∞ ρ) (hρs : tsupport ρ ⊆ e.source) :
    ∃ η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport ρ ∧ tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
        ∀ z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, η z = ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  let K := Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport ρ
  have hK : IsCompact K := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.chartCoordinateForward_compact V e (isClosed_tsupport ρ).isCompact hρs
  have hKD : K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hρs hx)
  obtain ⟨ψ, hψc, hψs, _, hψnear⟩ :=
    ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hK (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hKD
  let w := fun z => (ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) : ℂ)
  let β := fun z => w z * ψ z
  have hw : ContDiffOn ℝ ∞ w (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
    projectiveGlobalScalar_smooth V e he (fun x => (ρ x : ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp hρ)
  have hβsmooth : ContDiff ℝ ∞ β := ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.smooth_mul_test w ψ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hw (ψ.smooth ⊤) hψs
  have hβ (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
      β z = (ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) : ℂ) := by
    change (ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) : ℂ) * ψ z = _
    by_cases hzero : ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 0
    · rw [hzero, Complex.ofReal_zero, zero_mul]
    · have hzK : z ∈ K := ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, subset_tsupport ρ hzero,
        Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hz⟩
      rw [(hψnear z hzK).eq_of_nhds]
      exact mul_one _
  have hβzero (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∉ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : β z = 0 := by
    change w z * ψ z = 0
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hψs ht)), mul_zero]
  have hβK : tsupport β ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hzD : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
      by_contra hnot
      exact hz (hβzero z hnot)
    have hρz : ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) ≠ 0 := by
      intro hzero
      apply hz
      rw [hβ z hzD, hzero, Complex.ofReal_zero]
    exact ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, subset_tsupport ρ hρz, Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z hzD⟩
  have hηK : tsupport (fun z => (β z).re) ⊆ K :=
    (tsupport_comp_subset (show Complex.re 0 = 0 from rfl) β).trans hβK
  refine ⟨fun z => (β z).re, Complex.reCLM.contDiff.comp hβsmooth,
    hK.of_isClosed_subset (isClosed_tsupport _) hηK, hηK, hηK.trans hKD, ?_⟩
  intro z hz
  change (β z).re = ρ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)
  rw [hβ z hz, Complex.ofReal_re]

end AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairSmooth

end

end OAI
