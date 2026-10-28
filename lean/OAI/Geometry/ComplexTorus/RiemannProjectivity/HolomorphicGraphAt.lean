import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldFinite
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt

/-! # Holomorphic Graph At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates

noncomputable section

/-! # RiemannProjectivity: projective coordinates of arbitrary holomorphic graphs -/

open Set Filter _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold _root_.Topology
open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone
attribute [local instance] Classical.propDecidable

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] {m n : ℕ}

abbrev model (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] :=
  Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

def embedding (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → Projectivization ℂ (Fin (m + 1) → ℂ) :=
  fun x => (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph m).symm (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x)

omit [IsIntegral X.left] [Smooth X.hom] in
theorem embedding_closed (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsClosedImmersion a.left] :
    Topology.IsClosedEmbedding (embedding a) :=
  (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph m).symm.isClosedEmbedding.comp
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion a)

def affinePair (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (Fin m → ℂ) × (Fin n → ℂ) :=
  (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap a i x, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap b j (f x))

theorem affinePair_mdifferentiableAt (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, model X)) (𝓘(ℂ, model Y)) f)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : embedding a x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (hy : embedding b (f x) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source) :
    MDifferentiableAt (𝓘(ℂ, model X)) (𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ))) (affinePair a b f i j) x :=
  (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap a i hx).prodMk_space
    ((AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap b j hy).comp x (hf x))

theorem affinePair_injective_derivative (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    [IsClosedImmersion a.left] (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, model X)) (𝓘(ℂ, model Y)) f)
    (i : Fin (m + 1)) (j : Fin (n + 1)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : embedding a x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (hy : embedding b (f x) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source) :
    Function.Injective (mfderiv (𝓘(ℂ, model X)) (𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ)))
      (affinePair a b f i j) x) := by
  have hfst : MDifferentiable (𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ))) (𝓘(ℂ, Fin m → ℂ)) Prod.fst :=
    mdifferentiable_iff_differentiable.mpr differentiable_fst
  have hchain := mfderiv_comp x (hfst (affinePair a b f i j x))
    (affinePair_mdifferentiableAt a b f hf i j x hx hy)
  have heq : Prod.fst ∘ affinePair a b f i j = AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.coordinatesOfSchemeMap a i := rfl
  rw [heq] at hchain
  intro v w hvw
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective a i hx
  rw [hchain]
  exact congrArg (mfderiv (𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ))) (𝓘(ℂ, Fin m → ℂ))
    Prod.fst (affinePair a b f i j x)) hvw

def graph (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Projectivization ℂ (Fin (m + 1) × Fin (n + 1) → ℂ) := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.segre (embedding a x) (embedding b (f x))

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
theorem graph_continuous (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsClosedImmersion a.left]
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion b.left]
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (hf : Continuous f) : Continuous (graph a b f) :=
  AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.continuous_segre.comp ((embedding_closed a).continuous.prodMk ((embedding_closed b).continuous.comp hf))

theorem graph_chart_data (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsClosedImmersion a.left]
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion b.left]
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, model X)) (𝓘(ℂ, model Y)) f)
    (ij : Fin (m + 1) × Fin (n + 1)) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hx : x ∈ ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartDomain (graph a b f) ij) :
    MDifferentiableAt (𝓘(ℂ, model X)) (𝓘(ℂ, {k : Fin (m + 1) × Fin (n + 1) // k ≠ ij} → ℂ))
      (ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (graph a b f) ij) x ∧
    Function.Injective (mfderiv (𝓘(ℂ, model X))
      (𝓘(ℂ, {k : Fin (m + 1) × Fin (n + 1) // k ≠ ij} → ℂ)) (ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (graph a b f) ij) x) := by
  obtain ⟨i, j⟩ := ij
  have hxy := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.inPatch_segre_iff i j _ _).mp hx
  let F := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.finAffineSegre i j ∘ affinePair a b f i j
  have hdF : MDifferentiableAt (𝓘(ℂ, model X))
      (𝓘(ℂ, {k : Fin (m + 1) × Fin (n + 1) // k ≠ (i, j)} → ℂ)) F x :=
    ((mdifferentiable_iff_differentiable.mpr (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.differentiable_finAffineSegre i j))
      (affinePair a b f i j x)).comp x (affinePair_mdifferentiableAt a b f hf i j x hxy.1 hxy.2)
  have hiF : Function.Injective (mfderiv (𝓘(ℂ, model X))
      (𝓘(ℂ, {k : Fin (m + 1) × Fin (n + 1) // k ≠ (i, j)} → ℂ)) F x) := by
    rw [show F = AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.finAffineSegre i j ∘ affinePair a b f i j from rfl, mfderiv_comp x
      ((mdifferentiable_iff_differentiable.mpr (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.differentiable_finAffineSegre i j)) _)
      (affinePair_mdifferentiableAt a b f hf i j x hxy.1 hxy.2), mfderiv_eq_fderiv]
    exact (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.fderiv_finAffineSegre_injective i j _).comp
      (affinePair_injective_derivative a b f hf i j x hxy.1 hxy.2)
  have heq : ProjectiveManifoldIs.Constructions.ProjectiveManifoldCone.chartMap (graph a b f) (i, j) =ᶠ[𝓝 x] F := by
    filter_upwards [((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j)).open_source.preimage
      (graph_continuous a b f hf.continuous)).mem_nhds hx] with y hy
    have hp := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.inPatch_segre_iff i j _ _).mp hy
    exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.projectiveChart_segre_fin i j hp.1 hp.2
  refine ⟨hdF.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq (I := 𝓘(ℂ, model X))
    (I' := 𝓘(ℂ, {k : Fin (m + 1) × Fin (n + 1) // k ≠ (i, j)} → ℂ))]
  exact hiF

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates
