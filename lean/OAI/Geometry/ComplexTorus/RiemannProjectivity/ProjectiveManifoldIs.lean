import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin

/-! # Projective Manifold Is -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone

noncomputable section

/-! # RiemannProjectivity: local equations and parameters for a projectively embedded complex manifold -/

open Set
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone
attribute [local instance] Classical.propDecidable

variable {V M ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) 1 M] [Fintype ι]

def chartDomain (f : M → Projectivization ℂ (ι → ℂ)) (i : ι) : Set M :=
  f ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source

def chartMap (f : M → Projectivization ℂ (ι → ℂ)) (i : ι) :
    M → ({j : ι // j ≠ i} → ℂ) := fun x => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i (f x)

omit [TopologicalSpace M] [Fintype ι] in
theorem chart_image (f : M → Projectivization ℂ (ι → ℂ)) (i : ι) :
    chartMap f i '' chartDomain f i = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i '' (range f ∩ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) := by
  change (fun x => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i (f x)) '' (f ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) = _
  rw [← image_image, image_preimage_eq_inter_range, inter_comm]

omit [Fintype ι] in
theorem chart_isEmbedding (f : M → Projectivization ℂ (ι → ℂ))
    (hf : Topology.IsEmbedding f) (i : ι) :
    Topology.IsEmbedding (fun x : chartDomain f i => chartMap f i x) :=
  (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).isEmbedding_restrict.comp (hf.restrictPreimage (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source)

theorem local_equations (f : M → Projectivization ℂ (ι → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ i x, x ∈ chartDomain f i →
      MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, {j : ι // j ≠ i} → ℂ)) (chartMap f i) x ∧
      Function.Injective (mfderiv (𝓘(ℂ, V)) (𝓘(ℂ, {j : ι // j ≠ i} → ℂ)) (chartMap f i) x))
    (v : ι → ℂ) (hv : v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (hv0 : v ≠ 0) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v := by
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone.holomorphicZeroSetAt_coordinateCone _ ?_ v hv hv0
  intro i p hp hi
  obtain ⟨x, rfl⟩ := hp
  rw [← chart_image]
  exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone.holomorphicZeroSetAt_manifold_image ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).open_source.preimage hf.continuous)
    (fun y hy => (hd i y hy).1.mdifferentiableWithinAt) (chart_isEmbedding f hf i) hi (hd i x hi).2

theorem local_parameters (f : M → Projectivization ℂ (ι → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ i x, x ∈ chartDomain f i →
      MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, {j : ι // j ≠ i} → ℂ)) (chartMap f i) x)
    (v : ι → ℂ) (hv : v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (hv0 : v ≠ 0) :
    ∃ (O : Set (ι → ℂ)) (U : Set (V × ℂ)) (φ : V × ℂ → (ι → ℂ)),
      IsOpen O ∧ v ∈ O ∧ IsOpen U ∧ DifferentiableOn ℂ φ U ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∩ O ⊆ φ '' U ∧ MapsTo φ U (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) ∧ InjOn φ U := by
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization.Constructions.Cone.local_parametrization_of_coordinateCone _ ?_ v hv hv0
  intro i p hp hi
  obtain ⟨x, rfl⟩ := hp
  have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone.local_parametrization_of_manifold_image (U := chartDomain f i)
    ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).open_source.preimage hf.continuous)
    (fun y hy => (hd i y hy).mdifferentiableWithinAt) (chart_isEmbedding f hf i) hi
  rw [chart_image, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone.projectiveChart_image_eq_preimage] at h
  exact h

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone
