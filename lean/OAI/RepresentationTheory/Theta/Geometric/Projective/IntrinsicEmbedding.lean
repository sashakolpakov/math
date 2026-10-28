import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness

/-! # Intrinsic Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.IntrinsicEmbedding

noncomputable section

/-! The actual projective embedding of an integral projective variety
has holomorphic affine charts with injective complex differential. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance nativeProjectiveIntegral : IsIntegral X.toOver.left := X.property
local instance nativeProjectiveSmooth : Smooth X.toOver.hom := X.presentation.smooth

abbrev ProjectiveAmbientCoordinates := Fin (X.presentation.projective.ambientDimension + 1)

def projectiveNativeEmbedding (x : X.analyticSpace) :
    Projectivization ℂ (ProjectiveAmbientCoordinates X → ℂ) :=
  (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph X.presentation.projective.ambientDimension).symm
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map X.presentation.projective.toOverHom x)

theorem projectiveNativeEmbedding_isClosedEmbedding : Topology.IsClosedEmbedding (projectiveNativeEmbedding X) := by
  let P := X.presentation.projective
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph P.ambientDimension).symm.isClosedEmbedding.comp
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion P.toOverHom)

def projectiveNativeFinCoordinates (i : ProjectiveAmbientCoordinates X) (x : X.analyticSpace) :
    Fin X.presentation.projective.ambientDimension → ℂ :=
  AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (projectiveNativeEmbedding X x)

theorem projectiveNativeFinCoordinates_holomorphic (i : ProjectiveAmbientCoordinates X) {x : X.analyticSpace}
    (hx : projectiveNativeEmbedding X x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    MDifferentiableAt (𝓘(ℂ, X.analyticModel))
      (𝓘(ℂ, Fin X.presentation.projective.ambientDimension → ℂ)) (projectiveNativeFinCoordinates X i) x :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap
    (X := X.toOver) X.presentation.projective.toOverHom i hx

theorem projectiveNativeFinCoordinates_derivative_injective (i : ProjectiveAmbientCoordinates X) {x : X.analyticSpace}
    (hx : projectiveNativeEmbedding X x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    Function.Injective (mfderiv (𝓘(ℂ, X.analyticModel))
      (𝓘(ℂ, Fin X.presentation.projective.ambientDimension → ℂ)) (projectiveNativeFinCoordinates X i) x) := by
  let P := X.presentation.projective
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective (X := X.toOver) P.toOverHom i hx

def projectiveNativeCoordinates (i : ProjectiveAmbientCoordinates X) (x : X.analyticSpace) :
    {j : ProjectiveAmbientCoordinates X // j ≠ i} → ℂ :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i (projectiveNativeFinCoordinates X i x)

theorem projectiveNativeCoordinates_eq (i : ProjectiveAmbientCoordinates X) (x : X.analyticSpace) :
    projectiveNativeCoordinates X i x = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i (projectiveNativeEmbedding X x) :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin_projectiveFinChart i _

theorem projectiveNativeCoordinates_holomorphic (i : ProjectiveAmbientCoordinates X) {x : X.analyticSpace}
    (hx : projectiveNativeEmbedding X x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) :
    MDifferentiableAt (𝓘(ℂ, X.analyticModel))
      (𝓘(ℂ, {j : ProjectiveAmbientCoordinates X // j ≠ i} → ℂ)) (projectiveNativeCoordinates X i) x :=
  ((mdifferentiable_iff_differentiable.mpr (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i).differentiable)
    (projectiveNativeFinCoordinates X i x)).comp x (projectiveNativeFinCoordinates_holomorphic X i hx)

theorem projectiveNativeCoordinates_derivative_injective (i : ProjectiveAmbientCoordinates X) {x : X.analyticSpace}
    (hx : projectiveNativeEmbedding X x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) :
    Function.Injective (mfderiv (𝓘(ℂ, X.analyticModel))
      (𝓘(ℂ, {j : ProjectiveAmbientCoordinates X // j ≠ i} → ℂ)) (projectiveNativeCoordinates X i) x) := by
  have hc := mfderiv_comp x
    ((mdifferentiable_iff_differentiable.mpr (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i).differentiable)
      (projectiveNativeFinCoordinates X i x)) (projectiveNativeFinCoordinates_holomorphic X i hx)
  change Function.Injective (mfderiv (𝓘(ℂ, X.analyticModel))
    (𝓘(ℂ, {j : ProjectiveAmbientCoordinates X // j ≠ i} → ℂ))
    ((AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i) ∘ projectiveNativeFinCoordinates X i) x)
  rw [hc, mfderiv_eq_fderiv, (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.expandFin i).fderiv]
  exact (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.contractFin_expandFin i).injective.comp (projectiveNativeFinCoordinates_derivative_injective X i hx)

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.IntrinsicEmbedding
