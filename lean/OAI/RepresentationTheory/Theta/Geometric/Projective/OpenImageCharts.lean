import OAI.RepresentationTheory.Theta.Geometric.Projective.IntrinsicEmbedding
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization

/-! # Open Image Charts -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.OpenImageCharts

noncomputable section

/-! Open subsets of an actual projective variety have embedded
holomorphic affine chart images and genuine local manifold parametrizations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Set X.analyticSpace)

def projectiveSubsetChartDomain (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X) : Set X.analyticSpace :=
  U ∩ IntrinsicEmbedding.projectiveNativeEmbedding X ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source

theorem projectiveSubsetChartDomain_isOpen (hU : IsOpen U) (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X) :
    IsOpen (projectiveSubsetChartDomain X U i) :=
  hU.inter ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).open_source.preimage (IntrinsicEmbedding.projectiveNativeEmbedding_isClosedEmbedding X).continuous)

theorem projectiveSubsetChart_image (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X) :
    IntrinsicEmbedding.projectiveNativeCoordinates X i '' projectiveSubsetChartDomain X U i =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i '' (IntrinsicEmbedding.projectiveNativeEmbedding X '' U ∩ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨IntrinsicEmbedding.projectiveNativeEmbedding X x, ⟨⟨x, hx.1, rfl⟩, hx.2⟩, (IntrinsicEmbedding.projectiveNativeCoordinates_eq X i x).symm⟩
  · rintro ⟨p, ⟨⟨x, hx, rfl⟩, hp⟩, rfl⟩
    exact ⟨x, ⟨hx, hp⟩, IntrinsicEmbedding.projectiveNativeCoordinates_eq X i x⟩

theorem projectiveSubsetChart_isEmbedding (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X) :
    Topology.IsEmbedding (fun x : projectiveSubsetChartDomain X U i => IntrinsicEmbedding.projectiveNativeCoordinates X i x) := by
  let c := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i
  have he := (IntrinsicEmbedding.projectiveNativeEmbedding_isClosedEmbedding X).isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ projectiveSubsetChartDomain X U i))
  have h := c.isEmbedding_restrict.comp (he.codRestrict c.source (fun x => x.property.2))
  have hfun : (fun x : projectiveSubsetChartDomain X U i => IntrinsicEmbedding.projectiveNativeCoordinates X i x) =
      fun x : projectiveSubsetChartDomain X U i => c (IntrinsicEmbedding.projectiveNativeEmbedding X x) := by
    funext x
    exact IntrinsicEmbedding.projectiveNativeCoordinates_eq X i x
  rw [hfun]
  exact h

theorem projectiveSubsetChart_holomorphic (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X) :
    MDifferentiableOn (𝓘(ℂ, X.analyticModel))
      (𝓘(ℂ, {j : IntrinsicEmbedding.ProjectiveAmbientCoordinates X // j ≠ i} → ℂ))
      (IntrinsicEmbedding.projectiveNativeCoordinates X i) (projectiveSubsetChartDomain X U i) :=
  fun _x hx => (IntrinsicEmbedding.projectiveNativeCoordinates_holomorphic X i hx.2).mdifferentiableWithinAt

theorem projectiveSubsetChart_local_equations (hU : IsOpen U) (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X)
    {x : X.analyticSpace} (hx : x ∈ projectiveSubsetChartDomain X U i) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (IntrinsicEmbedding.projectiveNativeCoordinates X i '' projectiveSubsetChartDomain X U i)
      (IntrinsicEmbedding.projectiveNativeCoordinates X i x) :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone.holomorphicZeroSetAt_manifold_image (projectiveSubsetChartDomain_isOpen X U hU i)
    (projectiveSubsetChart_holomorphic X U i) (projectiveSubsetChart_isEmbedding X U i) hx
    (IntrinsicEmbedding.projectiveNativeCoordinates_derivative_injective X i hx.2)

theorem projectiveSubsetChart_local_parametrization (hU : IsOpen U) (i : IntrinsicEmbedding.ProjectiveAmbientCoordinates X)
    {x : X.analyticSpace} (hx : x ∈ projectiveSubsetChartDomain X U i) :
    ∃ (O : Set ({j : IntrinsicEmbedding.ProjectiveAmbientCoordinates X // j ≠ i} → ℂ))
      (V : Set X.analyticModel) (φ : X.analyticModel → ({j : IntrinsicEmbedding.ProjectiveAmbientCoordinates X // j ≠ i} → ℂ)),
      IsOpen O ∧ IntrinsicEmbedding.projectiveNativeCoordinates X i x ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
      (IntrinsicEmbedding.projectiveNativeCoordinates X i '' projectiveSubsetChartDomain X U i) ∩ O ⊆ φ '' V ∧
      MapsTo φ V (IntrinsicEmbedding.projectiveNativeCoordinates X i '' projectiveSubsetChartDomain X U i) ∧ InjOn φ V :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone.local_parametrization_of_manifold_image (projectiveSubsetChartDomain_isOpen X U hU i)
    (projectiveSubsetChart_holomorphic X U i) (projectiveSubsetChart_isEmbedding X U i) hx

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.OpenImageCharts
