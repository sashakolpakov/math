import OAI.Analysis.HodgeTheory.Decomposition.GardingExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful

/-! # Regularity Cutoffs -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RegularityCutoffs.Constructions

noncomputable section

/-! Nested real cutoffs in an actual chart, simultaneously respecting
the manifold neighborhood and the principal-coefficient agreement region. -/

open Set
open scoped _root_.Topology SchwartzMap ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction

theorem schwartz_realPart_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : 𝓢(E, ℂ)) : tsupport (fun x => (g x).re) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  apply subset_tsupport g
  intro h
  apply hx
  change (g x).re = 0
  rw [h, Complex.zero_re]

theorem schwartz_realPart_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : 𝓢(E, ℂ)) (hg : HasCompactSupport g) : HasCompactSupport (fun x => (g x).re) :=
  hg.of_isClosed_subset (isClosed_tsupport _) (schwartz_realPart_tsupport g)

theorem exists_projective_regularity_cutoffs (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {W : Set V.analyticSpace} (hW : IsOpen W) (hzW : MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ W)
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (hA : A =ᶠ[𝓝 z] GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n) :
    ∃ T : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), IsOpen T ∧ z ∈ T ∧ T ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e T ⊆ W ∧
      (∀ x ∈ T, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x) ∧
      ∃ τ : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport τ ∧
        tsupport τ ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧ (∀ x, τ x = Complex.ofReal (τ x).re) ∧
        (∀ x ∈ T, τ x = 1) ∧
        ∃ g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g ∧ tsupport g ⊆ T ∧
          (∀ x, g x = Complex.ofReal (g x).re) ∧ g =ᶠ[𝓝 z] 1 := by
  obtain ⟨P, hPA, hP, hzP⟩ := mem_nhds_iff.mp hA
  let Q := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) ∩ MeasureVolume.Constructions.chartCoordinateInverse V e ⁻¹' W
  have hQ : IsOpen Q := (MeasureVolume.Constructions.chartCoordinateInverse_continuousOn V e).isOpen_inter_preimage
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hW
  have hzQ : z ∈ Q := ⟨hz, hzW⟩
  let R := Q ∩ P
  have hR : IsOpen R := hQ.inter hP
  have hzR : z ∈ R := ⟨hzQ, hzP⟩
  obtain ⟨τ, hτc, hτR, hτreal, hτnear⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (K := {z}) isCompact_singleton hR (by simpa only [singleton_subset_iff] using hzR)
  have hτz : (τ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 z] 1 := hτnear z (mem_singleton z)
  obtain ⟨S, hSτ, hS, hzS⟩ := mem_nhds_iff.mp hτz
  let T := R ∩ S
  have hT : IsOpen T := hR.inter hS
  have hzT : z ∈ T := ⟨hzR, hzS⟩
  have hTchart : T ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun _ hx => hx.1.1.1
  obtain ⟨g, hgc, hgT, hgreal, hgnear⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (K := {z}) isCompact_singleton hT (by simpa only [singleton_subset_iff] using hzT)
  refine ⟨T, hT, hzT, hTchart, ?_, ?_, τ, hτc,
    hτR.trans (fun _ hx => hx.1.1), hτreal, ?_, g, hgc, hgT, hgreal, hgnear z (mem_singleton z)⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hy.1.1.2
  · intro x hx
    exact hPA hx.1.2
  · intro x hx
    exact hSτ hx.2

end

end OAI.Analysis.HodgeTheory.Decomposition.RegularityCutoffs.Constructions
