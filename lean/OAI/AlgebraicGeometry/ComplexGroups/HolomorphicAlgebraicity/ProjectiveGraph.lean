import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BranchExtension
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreProjection
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearAnalyticImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeParametrization
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicDimension
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AlgebraicCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveReindex
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreClosedSubscheme
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteNormalIso
import Mathlib.Topology.LocalAtTarget

/-! # Projective Graph -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph

/-!
# HolomorphicAlgebraicity: algebraicity of holomorphic group homomorphisms

The statement specification is `Statements/HolomorphicAlgebraicity.lean`; it is not imported,
because its proof is a placeholder. The additional `MFDeriv.Basic` import
supplies the `MDifferentiable` predicate used by that specification.

The proof constructs the compact holomorphic graph in Segre projective
coordinates. Finite cone projections and holomorphic coefficient extension
give exact homogeneous polynomial equations, including at exceptional fibers
and the vertex. These equations define a reduced closed graph scheme in the
product of the original abelian varieties.

The graph projection is proper and bijective on complex points. Its diagonal
is surjective, so the projection is universally injective and finite. In
characteristic zero its generic stalk map is an isomorphism. Integral
closedness of the smooth source's affine coordinate rings then makes the
projection an isomorphism. Composing its inverse with the other projection
gives the required algebraic map; equality on complex points proves that it
preserves the algebraic group law.

The final theorem has the specification's original name and signature. No
proposition interface for algebraicity is used as an assumption.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.Manifold _root_.CategoryTheory.MonObj

namespace Constructions

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsProper A.toOver.hom :=
  A.variety.presentation.projective.isProper

abbrev Points (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver

abbrev Model (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ

abbrev ProjectiveCoordinates (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin (A.variety.presentation.projective.ambientDimension + 1)

abbrev AffineProjectiveModel (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin A.variety.presentation.projective.ambientDimension → ℂ

/-- The chosen algebraic projective presentation induces an ordinary
projective embedding of the native complex-point space. -/
noncomputable def projectiveEmbedding (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (x : Points A) :
    Projectivization ℂ (ProjectiveCoordinates A → ℂ) :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph A.variety.presentation.projective.ambientDimension).symm
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map A.variety.presentation.projective.toOverHom x)

theorem isClosedEmbedding_projectiveEmbedding (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Topology.IsClosedEmbedding (projectiveEmbedding A) := by
  let P := A.variety.presentation.projective
  let : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  exact (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph P.ambientDimension).symm.isClosedEmbedding.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion P.toOverHom)

/-- The original projective presentation in its standard affine coordinates. -/
noncomputable def affineProjectiveEmbedding (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : ProjectiveCoordinates A) (x : Points A) :
    Fin A.variety.presentation.projective.ambientDimension → ℂ :=
  ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (projectiveEmbedding A x)

theorem mdifferentiableAt_affineProjectiveEmbedding (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : ProjectiveCoordinates A) {x : Points A}
    (hx : projectiveEmbedding A x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    MDifferentiableAt (𝓘(ℂ, Model A))
      (𝓘(ℂ, Fin A.variety.presentation.projective.ambientDimension → ℂ))
      (affineProjectiveEmbedding A i) x :=
  ProjectiveCoordinates.mdifferentiableAt_coordinatesOfSchemeMap
    (X := A.toOver) A.variety.presentation.projective.toOverHom i hx

theorem mfderiv_affineProjectiveEmbedding_injective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (i : ProjectiveCoordinates A) {x : Points A}
    (hx : projectiveEmbedding A x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    Function.Injective (mfderiv (𝓘(ℂ, Model A))
      (𝓘(ℂ, Fin A.variety.presentation.projective.ambientDimension → ℂ))
      (affineProjectiveEmbedding A i) x) := by
  let φ : A.toOver ⟶ Over.mk
      (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase A.variety.presentation.projective.ambientDimension) :=
    A.variety.presentation.projective.toOverHom
  let : IsClosedImmersion φ.left :=
    A.variety.presentation.projective.closedImmersion
  exact ProjectiveCoordinates.mfderiv_coordinatesOfSchemeMap_injective
    φ i hx

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}

/-- The original holomorphic graph in a pair of standard projective patches. -/
noncomputable def affineProjectiveGraph (f : Points A →* Points B)
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) (x : Points A) :
    AffineProjectiveModel A × AffineProjectiveModel B :=
  (affineProjectiveEmbedding A i x, affineProjectiveEmbedding B j (f x))

theorem mdifferentiableAt_affineProjectiveGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) {x : Points A}
    (hx : projectiveEmbedding A x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (hfx : projectiveEmbedding B (f x) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source) :
    MDifferentiableAt (𝓘(ℂ, Model A))
      (𝓘(ℂ, AffineProjectiveModel A × AffineProjectiveModel B))
      (affineProjectiveGraph f i j) x :=
  (mdifferentiableAt_affineProjectiveEmbedding A i hx).prodMk_space
    ((mdifferentiableAt_affineProjectiveEmbedding B j hfx).comp x (hf x))

theorem mfderiv_affineProjectiveGraph_injective
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) {x : Points A}
    (hx : projectiveEmbedding A x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (hfx : projectiveEmbedding B (f x) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source) :
    Function.Injective (mfderiv (𝓘(ℂ, Model A))
      (𝓘(ℂ, AffineProjectiveModel A × AffineProjectiveModel B))
      (affineProjectiveGraph f i j) x) := by
  have hfst : MDifferentiable
      (𝓘(ℂ, AffineProjectiveModel A × AffineProjectiveModel B))
      (𝓘(ℂ, AffineProjectiveModel A)) Prod.fst :=
    mdifferentiable_iff_differentiable.mpr differentiable_fst
  have hchain := mfderiv_comp x (hfst (affineProjectiveGraph f i j x))
    (mdifferentiableAt_affineProjectiveGraph f hf i j hx hfx)
  have heq : Prod.fst ∘ affineProjectiveGraph f i j = affineProjectiveEmbedding A i := rfl
  rw [heq] at hchain
  intro v w hvw
  apply mfderiv_affineProjectiveEmbedding_injective A i hx
  rw [hchain]
  exact congrArg (mfderiv
    (𝓘(ℂ, AffineProjectiveModel A × AffineProjectiveModel B))
    (𝓘(ℂ, AffineProjectiveModel A)) Prod.fst (affineProjectiveGraph f i j x)) hvw

/-- The graph of the given map in a single projective ambient space, using
the actual projective presentations and the Segre map. -/
noncomputable def projectiveGraphMap (f : Points A →* Points B) (x : Points A) :
    Projectivization ℂ (ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ) :=
  SegreAt.Constructions.Segre.segre (projectiveEmbedding A x) (projectiveEmbedding B (f x))

/-- A holomorphic homomorphism is continuous on the native analytic spaces. -/
theorem continuous_of_holomorphic
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    Continuous (fun x => f x) :=
  hf.continuous

/-- The part of the original source whose graph lies in the chosen pair of
standard projective coordinate patches. -/
def affineProjectiveGraphDomain (f : Points A →* Points B)
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) : Set (Points A) :=
  {x | projectiveEmbedding A x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source ∧
    projectiveEmbedding B (f x) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).source}

theorem isOpen_affineProjectiveGraphDomain
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) :
    IsOpen (affineProjectiveGraphDomain f i j) :=
  ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage
    (isClosedEmbedding_projectiveEmbedding A).continuous).inter
      ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j).open_source.preimage
        ((isClosedEmbedding_projectiveEmbedding B).continuous.comp hf.continuous))

theorem isEmbedding_affineProjectiveGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) :
    Topology.IsEmbedding (fun x : affineProjectiveGraphDomain f i j =>
      affineProjectiveGraph f i j x) := by
  let H := fun x : Points A => (projectiveEmbedding A x, projectiveEmbedding B (f x))
  have hH : Topology.IsEmbedding H :=
    ((isClosedEmbedding_projectiveEmbedding A).isEmbedding.prodMap
      (isClosedEmbedding_projectiveEmbedding B).isEmbedding).comp
        (_root_.isEmbedding_graph hf.continuous)
  let c := (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).prod (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart j)
  exact c.isEmbedding_restrict.comp (hH.restrictPreimage c.source)

/-- The given holomorphic graph has actual local holomorphic equations in
every pair of standard projective affine charts. -/
theorem holomorphicZeroSetAt_affineProjectiveGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A} (hx : x ∈ affineProjectiveGraphDomain f i j) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      (affineProjectiveGraph f i j '' affineProjectiveGraphDomain f i j)
      (affineProjectiveGraph f i j x) := by
  apply ManifoldImage.Constructions.Cone.holomorphicZeroSetAt_manifold_image
    (isOpen_affineProjectiveGraphDomain f hf i j)
    (fun y hy => (mdifferentiableAt_affineProjectiveGraph f hf i j hy.1 hy.2).mdifferentiableWithinAt)
    (isEmbedding_affineProjectiveGraph f hf i j) hx
  exact mfderiv_affineProjectiveGraph_injective f hf i j hx.1 hx.2

abbrev SegreAffineModel (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) :=
  {ab : ProjectiveCoordinates A × ProjectiveCoordinates B // ab ≠ (i, j)} → ℂ

noncomputable def segreAffineGraph (f : Points A →* Points B)
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) :
    Points A → SegreAffineModel i j :=
  SegreAt.Constructions.Segre.finAffineSegre i j ∘ affineProjectiveGraph f i j

theorem mdifferentiableAt_segreAffineGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A} (hx : x ∈ affineProjectiveGraphDomain f i j) :
    MDifferentiableAt (𝓘(ℂ, Model A)) (𝓘(ℂ, SegreAffineModel i j))
      (segreAffineGraph f i j) x :=
  ((mdifferentiable_iff_differentiable.mpr (SegreAt.Constructions.Segre.differentiable_finAffineSegre i j))
    (affineProjectiveGraph f i j x)).comp x
      (mdifferentiableAt_affineProjectiveGraph f hf i j hx.1 hx.2)

theorem mfderiv_segreAffineGraph_injective
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A} (hx : x ∈ affineProjectiveGraphDomain f i j) :
    Function.Injective (mfderiv (𝓘(ℂ, Model A)) (𝓘(ℂ, SegreAffineModel i j))
      (segreAffineGraph f i j) x) := by
  rw [segreAffineGraph, mfderiv_comp x
    ((mdifferentiable_iff_differentiable.mpr (SegreAt.Constructions.Segre.differentiable_finAffineSegre i j))
      (affineProjectiveGraph f i j x))
    (mdifferentiableAt_affineProjectiveGraph f hf i j hx.1 hx.2)]
  rw [mfderiv_eq_fderiv]
  exact (SegreAt.Constructions.Segre.fderiv_finAffineSegre_injective i j _).comp
    (mfderiv_affineProjectiveGraph_injective f hf i j hx.1 hx.2)

theorem holomorphicZeroSetAt_segreAffineGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A} (hx : x ∈ affineProjectiveGraphDomain f i j) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      (segreAffineGraph f i j '' affineProjectiveGraphDomain f i j)
      (segreAffineGraph f i j x) := by
  apply ManifoldImage.Constructions.Cone.holomorphicZeroSetAt_manifold_image
    (isOpen_affineProjectiveGraphDomain f hf i j)
    (fun y hy => (mdifferentiableAt_segreAffineGraph f hf i j hy).mdifferentiableWithinAt)
    ((SegreAt.Constructions.Segre.isEmbedding_finAffineSegre i j).comp (isEmbedding_affineProjectiveGraph f hf i j)) hx
  exact mfderiv_segreAffineGraph_injective f hf i j hx

theorem segreAffineGraph_eq_projectiveChart
    (f : Points A →* Points B) (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A} (hx : x ∈ affineProjectiveGraphDomain f i j) :
    segreAffineGraph f i j x =
      ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j) (projectiveGraphMap f x) :=
  (SegreAt.Constructions.Segre.projectiveChart_segre_fin i j hx.1 hx.2).symm

theorem segreAffineGraph_image_eq_projectiveChart
    (f : Points A →* Points B) (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B) :
    segreAffineGraph f i j '' affineProjectiveGraphDomain f i j =
      ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j) ''
        (Set.range (projectiveGraphMap f) ∩ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j)).source) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨projectiveGraphMap f x, ⟨⟨x, rfl⟩, ?_⟩,
      (segreAffineGraph_eq_projectiveChart f i j hx).symm⟩
    exact (SegreAt.Constructions.Segre.inPatch_segre_iff i j _ _).mpr hx
  · rintro ⟨p, ⟨⟨x, rfl⟩, hp⟩, rfl⟩
    have hx : x ∈ affineProjectiveGraphDomain f i j :=
      (SegreAt.Constructions.Segre.inPatch_segre_iff i j _ _).mp hp
    exact ⟨x, hx, segreAffineGraph_eq_projectiveChart f i j hx⟩

/-- Local holomorphic equations for the actual closed graph in its single
projective ambient space, in every standard affine coordinate patch. -/
theorem holomorphicZeroSetAt_projectiveGraph_chart
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (i : ProjectiveCoordinates A) (j : ProjectiveCoordinates B)
    {x : Points A}
    (hx : projectiveGraphMap f x ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j)).source) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j) ''
        (Set.range (projectiveGraphMap f) ∩ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j)).source))
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart (i, j) (projectiveGraphMap f x)) := by
  have hx' : x ∈ affineProjectiveGraphDomain f i j :=
    (SegreAt.Constructions.Segre.inPatch_segre_iff i j _ _).mp hx
  have h := holomorphicZeroSetAt_segreAffineGraph f hf i j hx'
  rwa [segreAffineGraph_image_eq_projectiveChart,
    segreAffineGraph_eq_projectiveChart f i j hx'] at h

/-- The actual affine cone on the projectively embedded original graph. -/
noncomputable def projectiveGraphCone (f : Points A →* Points B) :
    Set (ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ) :=
  ProjectiveCone.Constructions.Cone.projectiveCone (Set.range (projectiveGraphMap f))

theorem zero_mem_projectiveGraphCone (f : Points A →* Points B) :
    0 ∈ projectiveGraphCone f := ProjectiveCone.Constructions.Cone.zero_mem_projectiveCone _

theorem smul_mem_projectiveGraphCone (f : Points A →* Points B) (c : ℂ)
    {v : ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ}
    (hv : v ∈ projectiveGraphCone f) : c • v ∈ projectiveGraphCone f :=
  ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _ c hv

/-- The cone on the given graph is locally holomorphic at every nonzero
vector, with all local-equation hypotheses discharged from the original data. -/
theorem holomorphicZeroSetAt_projectiveGraphCone
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (v : ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ)
    (hv : v ∈ projectiveGraphCone f) (hv0 : v ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (projectiveGraphCone f) v := by
  apply CoordinateCone.Constructions.Cone.holomorphicZeroSetAt_coordinateCone _ ?_ v hv hv0
  intro ij p hp hpatch
  obtain ⟨x, rfl⟩ := hp
  exact holomorphicZeroSetAt_projectiveGraph_chart f hf ij.1 ij.2 hpatch

theorem local_parametrization_projectiveGraphCone
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (v : ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ)
    (hv : v ∈ projectiveGraphCone f) (hv0 : v ≠ 0) :
    ∃ (O : Set (ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ))
        (V : Set (Model A × ℂ))
        (φ : Model A × ℂ → (ProjectiveCoordinates A × ProjectiveCoordinates B → ℂ)),
      IsOpen O ∧ v ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ φ V ∧
      projectiveGraphCone f ∩ O ⊆ φ '' V ∧ Set.MapsTo φ V (projectiveGraphCone f) ∧ Set.InjOn φ V := by
  apply ConeParametrization.Constructions.Cone.local_parametrization_of_coordinateCone _ _ v hv hv0
  intro ij p hp hpatch
  obtain ⟨x, rfl⟩ := hp
  have hx : x ∈ affineProjectiveGraphDomain f ij.1 ij.2 :=
    (SegreAt.Constructions.Segre.inPatch_segre_iff ij.1 ij.2 _ _).mp hpatch
  have hparam := ManifoldImage.Constructions.Cone.local_parametrization_of_manifold_image
    (isOpen_affineProjectiveGraphDomain f hf ij.1 ij.2)
    (fun y hy => (mdifferentiableAt_segreAffineGraph f hf ij.1 ij.2 hy).mdifferentiableWithinAt)
    ((SegreAt.Constructions.Segre.isEmbedding_finAffineSegre ij.1 ij.2).comp
      (isEmbedding_affineProjectiveGraph f hf ij.1 ij.2)) hx
  have himage : segreAffineGraph f ij.1 ij.2 '' affineProjectiveGraphDomain f ij.1 ij.2 =
      (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart ij).symm ⁻¹' Set.range (projectiveGraphMap f) :=
    (segreAffineGraph_image_eq_projectiveChart f ij.1 ij.2).trans
      (CoordinateCone.Constructions.Cone.projectiveChart_image_eq_preimage ij _)
  simpa only [himage, segreAffineGraph_eq_projectiveChart f ij.1 ij.2 hx] using hparam

theorem continuous_projectiveGraphMap
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    Continuous (projectiveGraphMap f) :=
  SegreAt.Constructions.Segre.continuous_segre.comp ((isClosedEmbedding_projectiveEmbedding A).continuous.prodMk
    ((isClosedEmbedding_projectiveEmbedding B).continuous.comp hf.continuous))

theorem projectiveGraphMap_injective (f : Points A →* Points B) :
    Function.Injective (projectiveGraphMap f) := by
  intro x y h
  have hpair : (projectiveEmbedding A x, projectiveEmbedding B (f x)) =
      (projectiveEmbedding A y, projectiveEmbedding B (f y)) := SegreAt.Constructions.Segre.segre_injective h
  exact (isClosedEmbedding_projectiveEmbedding A).injective (congrArg Prod.fst hpair)

/-- The original holomorphic graph is a closed embedded compact subset of
one ordinary complex projective space. -/
theorem isClosedEmbedding_projectiveGraphMap
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    Topology.IsClosedEmbedding (projectiveGraphMap f) := by
  let : CompactSpace (Points A) :=
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_compactSpace A.variety.presentation
  exact (continuous_projectiveGraphMap f hf).isClosedEmbedding (projectiveGraphMap_injective f)

theorem isClosed_projectiveGraphCone
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    IsClosed (projectiveGraphCone f) :=
  ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ (isClosedEmbedding_projectiveGraphMap f hf).isClosed_range

theorem projectiveGraphCone_subset_segreCone (f : Points A →* Points B) :
    projectiveGraphCone f ⊆ ProjectiveCone.Constructions.Cone.projectiveCone
      (Set.range (fun pq : Projectivization ℂ (ProjectiveCoordinates A → ℂ) ×
        Projectivization ℂ (ProjectiveCoordinates B → ℂ) => SegreAt.Constructions.Segre.segre pq.1 pq.2)) := by
  intro v hv hv0
  obtain ⟨x, hx⟩ := hv hv0
  exact ⟨(projectiveEmbedding A x, projectiveEmbedding B (f x)), hx⟩

theorem rankTwoCenter_not_mem_projectiveGraphCone (f : Points A →* Points B)
    (a₀ a₁ : ProjectiveCoordinates A) (b₀ b₁ : ProjectiveCoordinates B)
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁ ∉ projectiveGraphCone f :=
  fun h => SegreProjection.Constructions.Segre.rankTwoCenter_not_mem_segreCone a₀ a₁ b₀ b₁ ha hb
    (projectiveGraphCone_subset_segreCone f h)

/-- A concrete projection of the original graph cone is proper and has finite
fibers. The diagonal rank-two center avoids the graph by the Segre minors. -/
theorem proper_finite_projectiveGraphCone_projection
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (a₀ a₁ : ProjectiveCoordinates A) (b₀ b₁ : ProjectiveCoordinates B)
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    let L := SegreProjection.Constructions.Segre.projectionAlong (a₀, b₀) (SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁)
    IsProperMap (fun v : projectiveGraphCone f => L v) ∧
      ∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.Finite := by
  let w := SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁
  have hw : w (a₀, b₀) = 1 := SegreProjection.Constructions.Segre.rankTwoCenter_head a₀ a₁ b₀ b₁ ha
  have hwS : w ∉ projectiveGraphCone f :=
    rankTwoCenter_not_mem_projectiveGraphCone f a₀ a₁ b₀ b₁ ha hb
  refine ⟨SegreProjection.Constructions.Segre.isProperMap_projectionAlong (isClosed_projectiveGraphCone f hf)
    (smul_mem_projectiveGraphCone f) (a₀, b₀) w hw hwS, ?_⟩
  intro y
  exact SegreProjection.Constructions.Segre.finite_projectionAlong_fiber (isClosed_projectiveGraphCone f hf)
    (smul_mem_projectiveGraphCone f) (a₀, b₀) w hw hwS
    (holomorphicZeroSetAt_projectiveGraphCone f hf) y

/-- The concrete projection of the original graph cone has actual local
holomorphic equations away from the vertex. -/
theorem holomorphicZeroSetAt_projectiveGraphCone_projection
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (a₀ a₁ : ProjectiveCoordinates A) (b₀ b₁ : ProjectiveCoordinates B)
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    (y : {ab : ProjectiveCoordinates A × ProjectiveCoordinates B // ab ≠ (a₀, b₀)} → ℂ)
    (hy : y ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      (SegreProjection.Constructions.Segre.projectionAlong (a₀, b₀) (SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁) '' projectiveGraphCone f) y :=
  LinearAnalyticImage.Constructions.Segre.holomorphicZeroSetAt_projectionAlong (isClosed_projectiveGraphCone f hf)
    (smul_mem_projectiveGraphCone f) (a₀, b₀) (SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁)
    (SegreProjection.Constructions.Segre.rankTwoCenter_head a₀ a₁ b₀ b₁ ha)
    (rankTwoCenter_not_mem_projectiveGraphCone f a₀ a₁ b₀ b₁ ha hb)
    (holomorphicZeroSetAt_projectiveGraphCone f hf) y hy

theorem closed_radial_projectiveGraphCone_projection
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (a₀ a₁ : ProjectiveCoordinates A) (b₀ b₁ : ProjectiveCoordinates B)
    (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    let L := SegreProjection.Constructions.Segre.projectionAlong (a₀, b₀) (SegreProjection.Constructions.Segre.rankTwoCenter a₀ a₁ b₀ b₁)
    IsClosed (L '' projectiveGraphCone f) ∧
      ∀ (c : ℂ) ⦃y⦄, y ∈ L '' projectiveGraphCone f → c • y ∈ L '' projectiveGraphCone f := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [Set.image_eq_range]
    have hp := (proper_finite_projectiveGraphCone_projection f hf a₀ a₁ b₀ b₁ ha hb).1
    exact hp.isClosedMap.isClosed_range
  · intro c y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨c • v, smul_mem_projectiveGraphCone f c hv, map_smul _ _ _⟩

/-- The original graph cone admits a proper finite linear projection onto
an entire complex coordinate space, with a global linear bound on its fibers. -/
theorem finite_surjective_projectiveGraphCone_projection
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ (d : ℕ) (L : ((ProjectiveCoordinates A × ProjectiveCoordinates B) → ℂ) →L[ℂ] (Fin d → ℂ)),
      IsProperMap (fun v : projectiveGraphCone f => L v) ∧
      (∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.Finite) ∧
      (∃ N : ℕ, ∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.ncard ≤ N) ∧
      L '' projectiveGraphCone f = Set.univ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ projectiveGraphCone f, ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨d, L, _, hp, hfin, hcard, honto, hbound⟩ :=
    ConeNormalization.Constructions.Cone.exists_finite_surjective_projection_finiteDimensional
      (zero_mem_projectiveGraphCone f) (isClosed_projectiveGraphCone f hf)
      (smul_mem_projectiveGraphCone f) (holomorphicZeroSetAt_projectiveGraphCone f hf)
  exact ⟨d, L, hp, hfin, hcard, honto, hbound⟩

theorem normalization_dimension_projectiveGraphCone
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    {d : ℕ}
    (L : ((ProjectiveCoordinates A × ProjectiveCoordinates B) → ℂ) →L[ℂ] (Fin d → ℂ))
    (hsurj : L '' projectiveGraphCone f = Set.univ)
    (hfinite : ∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.Finite) :
    d = Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom + 1 := by
  have hne : ∃ v ∈ projectiveGraphCone f, v ≠ 0 :=
    ConeParametrization.Constructions.Cone.exists_nonzero_mem_projectiveCone ⟨projectiveGraphMap f 1, Set.mem_range_self 1⟩
  have hdim := HolomorphicDimension.Constructions.Dimension.finrank_eq_of_finite_surjective_parametrized_set
    (E := Model A × ℂ) L hsurj hfinite hne (local_parametrization_projectiveGraphCone f hf)
  simpa only [Model, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin,
    Module.finrank_self] using hdim.symm

theorem finite_surjective_projectiveGraphCone_projection_fixed_dimension
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ L : ((ProjectiveCoordinates A × ProjectiveCoordinates B) → ℂ) →L[ℂ]
        (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom + 1) → ℂ),
      IsProperMap (fun v : projectiveGraphCone f => L v) ∧
      (∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.Finite) ∧
      (∃ N : ℕ, ∀ y, {v | v ∈ projectiveGraphCone f ∧ L v = y}.ncard ≤ N) ∧
      L '' projectiveGraphCone f = Set.univ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ projectiveGraphCone f, ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨d, L, hp, hfinite, hcard, hsurj, hbound⟩ :=
    finite_surjective_projectiveGraphCone_projection f hf
  have hd := normalization_dimension_projectiveGraphCone f hf L hsurj hfinite
  subst d
  exact ⟨L, hp, hfinite, hcard, hsurj, hbound⟩

/-- The original holomorphic graph cone is exactly the zero locus of finitely
many homogeneous polynomials, including at the cone vertex. -/
theorem finite_homogeneous_equations_projectiveGraphCone
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ Q : Finset (MvPolynomial (ProjectiveCoordinates A × ProjectiveCoordinates B) ℂ),
      (∀ q ∈ Q, ∃ d, q.IsHomogeneous d) ∧
      projectiveGraphCone f = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} := by
  obtain ⟨L, _, hfinite, _, hsurj, C, _, hbound⟩ :=
    finite_surjective_projectiveGraphCone_projection_fixed_dimension f hf
  have hker : ∀ v ∈ projectiveGraphCone f, L v = 0 → v = 0 := by
    intro v hv hLv
    apply norm_le_zero_iff.mp
    simpa only [hLv, norm_zero, mul_zero] using hbound v hv
  have hdim : Module.finrank ℂ (Model A × ℂ) =
      Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom + 1) → ℂ) := by
    simp only [Model, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin, Module.finrank_self]
  exact AlgebraicCone.Constructions.Cone.finite_equations_of_parametrized_cone (Nat.zero_lt_succ _) hdim
    (zero_mem_projectiveGraphCone f) (isClosed_projectiveGraphCone f hf)
    (smul_mem_projectiveGraphCone f) (holomorphicZeroSetAt_projectiveGraphCone f hf)
    L hker hfinite hsurj (local_parametrization_projectiveGraphCone f hf)

/-- The actual projective holomorphic graph is a homogeneous algebraic zero
locus in its Segre projective coordinates. -/
theorem projective_equations_projectiveGraph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ (Q : Finset (MvPolynomial (ProjectiveCoordinates A × ProjectiveCoordinates B) ℂ))
      (degree : Q → ℕ) (hQ : ∀ q : Q, q.val.IsHomogeneous (degree q)),
      Set.range (projectiveGraphMap f) = Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus
        (fun q : Q => q.val) degree hQ := by
  obtain ⟨Q, hQ, hcone⟩ := finite_homogeneous_equations_projectiveGraphCone f hf
  choose degree hdegree using fun q : Q => hQ q.val q.property
  refine ⟨Q, degree, hdegree, ?_⟩
  ext p
  have heq : p.rep ∈ projectiveGraphCone f ↔
      ∀ q ∈ Q, MvPolynomial.eval p.rep q = 0 := by
    rw [hcone]
    rfl
  rw [projectiveGraphCone, ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff _ p.rep p.rep_nonzero, p.mk_rep] at heq
  rw [← p.mk_rep, Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
  simpa only [p.mk_rep, Subtype.forall] using heq

/-- A reduced, proper algebraic scheme whose projective complex points are
exactly the original holomorphic graph in relabeled Segre coordinates. -/
theorem exists_reduced_projective_graph_scheme
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ (n : ℕ) (e : (ProjectiveCoordinates A × ProjectiveCoordinates B) ≃ Fin (n + 1))
      (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)),
      IsReduced X.left ∧ IsClosedImmersion i.left ∧ IsProper X.hom ∧
      ∀ p : Projectivization ℂ ((ProjectiveCoordinates A × ProjectiveCoordinates B) → ℂ),
        Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n (ProjectiveReindex.Constructions.Algebraization.reindexProjective e p) ∈
          Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔ p ∈ Set.range (projectiveGraphMap f) := by
  obtain ⟨Q, degree, hQ, heq⟩ := projective_equations_projectiveGraph f hf
  obtain ⟨n, e, X, i, hX, hi, hp, hpoints⟩ :=
    ProjectiveReindex.Constructions.Algebraization.exists_reduced_projective_subscheme_finite_coordinates
      (fun q : Q => q.val) degree hQ
  refine ⟨n, e, X, i, hX, hi, hp, ?_⟩
  intro p
  rw [hpoints, heq]

/-- The graph is the exact complex-point locus of a reduced closed subscheme
of the product of the two original abelian varieties. -/
theorem exists_reduced_closed_graph_subscheme
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : Z ⟶ (A.toOver ⊗ B.toOver)),
      IsReduced Z.left ∧ IsClosedImmersion i.left ∧ IsProper Z.hom ∧
      ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A.toOver ⊗ B.toOver),
        p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔
          f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CartesianMonoidalCategory.fst A.toOver B.toOver) p) =
            ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CartesianMonoidalCategory.snd A.toOver B.toOver) p := by
  let π₁ := CartesianMonoidalCategory.fst A.toOver B.toOver
  let π₂ := CartesianMonoidalCategory.snd A.toOver B.toOver
  let a := π₁ ≫ A.variety.presentation.projective.toOverHom
  let b := π₂ ≫ B.variety.presentation.projective.toOverHom
  obtain ⟨Q, degree, hQ, hgraph⟩ := projective_equations_projectiveGraph f hf
  obtain ⟨Z, i, hZ, hi, himage⟩ := SegreClosedSubscheme.Constructions.Algebraization.exists_reduced_closed_subscheme_of_segre_equations
    a b (fun q : Q => q.val) degree hQ
  let : IsClosedImmersion i.left := hi
  have hproperProd : IsProper (A.toOver ⊗ B.toOver).hom := by dsimp; infer_instance
  let : IsProper (A.toOver ⊗ B.toOver).hom := hproperProd
  have hproperZ : IsProper Z.hom := by
    rw [← i.w]
    infer_instance
  refine ⟨Z, i, hZ, hi, hproperZ, ?_⟩
  intro p
  have hg : SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps a b p =
      SegreAt.Constructions.Segre.segre (projectiveEmbedding A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))
        (projectiveEmbedding B (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p)) := by
    simp only [a, b, SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps]
    rfl
  rw [himage]
  change SegreClosedSubscheme.Constructions.Algebraization.segreOfSchemeMaps a b p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus
    (fun q : Q => q.val) degree hQ ↔ _
  rw [← hgraph, hg]
  constructor
  · rintro ⟨x, hx⟩
    have heq : (projectiveEmbedding A x, projectiveEmbedding B (f x)) =
        (projectiveEmbedding A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p),
          projectiveEmbedding B (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p)) :=
      SegreAt.Constructions.Segre.segre_injective hx
    have hx₁ : x = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p :=
      (isClosedEmbedding_projectiveEmbedding A).injective (congrArg Prod.fst heq)
    have hx₂ : f x = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₂ p :=
      (isClosedEmbedding_projectiveEmbedding B).injective (congrArg Prod.snd heq)
    rwa [hx₁] at hx₂
  · intro h
    refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p, ?_⟩
    change SegreAt.Constructions.Segre.segre (projectiveEmbedding A (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))
      (projectiveEmbedding B (f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map π₁ p))) = _
    rw [h]

/-- The algebraic graph supplies a proper morphism to the source, bijective
on complex points, together with its algebraic projection to the target. -/
theorem exists_proper_graph_projection
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : Z ⟶ A.toOver) (q : Z ⟶ B.toOver),
      IsReduced Z.left ∧ IsProper Z.hom ∧ IsProper p.left ∧
      Function.Bijective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p) ∧
      ∀ z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p z) := by
  obtain ⟨Z, i, hZ, hi, hproperZ, hgraph⟩ := exists_reduced_closed_graph_subscheme f hf
  let : IsClosedImmersion i.left := hi
  let : Mono i := Over.mono_of_mono_left i
  let π₁ := CartesianMonoidalCategory.fst A.toOver B.toOver
  let π₂ := CartesianMonoidalCategory.snd A.toOver B.toOver
  let p := i ≫ π₁
  let q := i ≫ π₂
  have hproperπ : IsProper π₁.left := by dsimp [π₁]; infer_instance
  let : IsProper π₁.left := hproperπ
  have hproperp : IsProper p.left := by
    change IsProper (i.left ≫ π₁.left)
    infer_instance
  have hrel (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p z) := by
    have h := (hgraph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i z)).mp ⟨z, rfl⟩
    exact h.symm
  refine ⟨Z, p, q, hZ, hproperZ, hproperp, ⟨?_, ?_⟩, hrel⟩
  · intro z w hzw
    apply (cancel_mono i).mp
    apply CartesianMonoidalCategory.hom_ext (z ≫ i) (w ≫ i)
    · exact hzw
    · change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q z = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map q w
      rw [hrel, hrel, hzw]
  · intro x
    let r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A.toOver ⊗ B.toOver) := CartesianMonoidalCategory.lift x (f x)
    have hr : r ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) := by
      apply (hgraph r).mpr
      change f (r ≫ π₁) = r ≫ π₂
      simp only [r, π₁, π₂, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, ?_⟩
    change (z ≫ i) ≫ π₁ = x
    change z ≫ i = r at hz
    rw [hz]
    exact CartesianMonoidalCategory.lift_fst x (f x)

/-- The original holomorphy assumption supplies the continuous derivative
needed for local inverse charts, in the actual native manifold structures. -/
theorem contMDiff_one_of_holomorphic
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ContMDiff (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) 1 (fun x => f x) := by
  apply contMDiff_iff.mpr
  refine ⟨hf.continuous, fun x y => ?_⟩
  have hc : ContinuousOn
      (fun z => f ((extChartAt (𝓘(ℂ, Model A)) x).symm z))
      (extChartAt (𝓘(ℂ, Model A)) x).target :=
    hf.continuous.comp_continuousOn
      (continuousOn_extChartAt_symm (I := 𝓘(ℂ, Model A)) x)
  apply HolomorphicRegularity.Constructions.Regularity.contDiffOn_one_of_differentiableOn_pi
    (hc.isOpen_inter_preimage (isOpen_extChartAt_target x) (isOpen_extChartAt_source y))
  exact (mdifferentiable_iff.mp hf).2 x y

/-- In the native manifold coordinates, the given holomorphic graph has
explicit finite local holomorphic equations. -/
theorem holomorphic_graph_coordinates
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (x : Points A) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
      {p : Model A × Model B |
        p.2 = extChartAt (𝓘(ℂ, Model B)) (f x)
          (f ((extChartAt (𝓘(ℂ, Model A)) x).symm p.1))}
      (extChartAt (𝓘(ℂ, Model A)) x x, extChartAt (𝓘(ℂ, Model B)) (f x) (f x)) := by
  let e := extChartAt (𝓘(ℂ, Model A)) x
  let e' := extChartAt (𝓘(ℂ, Model B)) (f x)
  let U : Set (Model A) := e.target ∩ e.symm ⁻¹' f ⁻¹' e'.source
  have hc : ContinuousOn (fun z => f (e.symm z)) e.target :=
    hf.continuous.comp_continuousOn
      (continuousOn_extChartAt_symm (I := 𝓘(ℂ, Model A)) x)
  have hU : IsOpen U := hc.isOpen_inter_preimage
    (isOpen_extChartAt_target x) (isOpen_extChartAt_source (f x))
  have hxU : e x ∈ U := by
    simp only [U, e, e', mfld_simps]
  have hd : DifferentiableOn ℂ (e' ∘ f ∘ e.symm) U :=
    (mdifferentiable_iff.mp hf).2 x (f x)
  have hgraph := ZeroLocus.Constructions.Cone.holomorphicZeroSetAt_graph hU hd hxU
  simpa only [e, e', Function.comp_apply, mfld_simps] using hgraph

/-- The graph in the product of the actual complex-point spaces is compact. -/
theorem isCompact_graph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    IsCompact (Set.range (fun x : Points A => (x, f x))) := by
  let : CompactSpace (Points A) :=
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_compactSpace A.variety.presentation
  exact isCompact_range (continuous_id.prodMk (continuous_of_holomorphic f hf))

/-- The graph is closed in the ordinary analytic topology. -/
theorem isClosed_graph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    IsClosed (Set.range (fun x : Points A => (x, f x))) := by
  let : T2Space (Points A) :=
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_t2Space A.variety.presentation
  let : T2Space (Points B) :=
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_t2Space B.variety.presentation
  exact (isCompact_graph f hf).isClosed

/-- The holomorphic graph map is a closed embedding of the native spaces. -/
theorem isClosedEmbedding_graph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    Topology.IsClosedEmbedding (fun x : Points A => (x, f x)) :=
  ⟨_root_.isEmbedding_graph (continuous_of_holomorphic f hf), isClosed_graph f hf⟩

/-- The graph map preserves complex differentiability. -/
theorem mdifferentiable_graph
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    MDifferentiable (𝓘(ℂ, Model A))
      ((𝓘(ℂ, Model A)).prod (𝓘(ℂ, Model B)))
      (fun x : Points A => (x, f x)) :=
  mdifferentiable_id.prodMk hf

/-- The graph map has injective complex differential at every point. -/
theorem graph_mfderiv_injective
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x))
    (x : Points A) :
    Function.Injective (mfderiv (𝓘(ℂ, Model A))
      ((𝓘(ℂ, Model A)).prod (𝓘(ℂ, Model B)))
      (fun y : Points A => (y, f y)) x) := by
  have hder : HasMFDerivAt (𝓘(ℂ, Model A))
      ((𝓘(ℂ, Model A)).prod (𝓘(ℂ, Model B)))
      (fun y : Points A => (y, f y)) x
      ((ContinuousLinearMap.id ℂ (Model A)).prod
        (mfderiv (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun y => f y) x)) :=
    (hasMFDerivAt_id x).prodMk (hf x).hasMFDerivAt
  rw [hder.mfderiv]
  intro u v huv
  exact congrArg Prod.fst huv

/-- Complex-valued points distinguish morphisms from a reduced finite-type
complex scheme into a separated finite-type complex scheme. -/
theorem schemeMap_ext
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (g h : X ⟶ Y)
    (hpoints : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map h x) : g = h := by
  have : LocallyOfFiniteType (g.left ≫ Y.hom) := by
    rw [Over.w]
    infer_instance
  ext1
  apply ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
      Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)
    have hp := congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => q.left (IsLocalRing.closedPoint ℂ))
      (hpoints p)
    change g.left ((pointOfClosedPoint X.hom x hx) (IsLocalRing.closedPoint ℂ)) =
      h.left ((pointOfClosedPoint X.hom x hx) (IsLocalRing.closedPoint ℂ)) at hp
    have hp_at : (pointOfClosedPoint X.hom x hx) (IsLocalRing.closedPoint ℂ) = x :=
      pointOfClosedPoint_apply (K := ℂ) X.hom x hx _
    exact (congrArg g.left hp_at).symm.trans (hp.trans (congrArg h.left hp_at))
  · rw [Over.w, Over.w]

/-- An algebraic map inducing a specified homomorphism preserves the
algebraic group law, since this can be checked on complex-valued points. -/
theorem isMonHom_of_map_eq
    (f : Points A →* Points B) (g : A.toOver ⟶ B.toOver)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x) : IsMonHom g := by
  have hg' (x : Points A) : x ≫ g = f x := hg x
  let : LocallyOfFiniteType (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)).hom := by dsimp; infer_instance
  let : IsReduced (𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)).left := by dsimp; infer_instance
  let : Smooth (A.toOver ⊗ A.toOver).hom := by dsimp; infer_instance
  let : IsReduced (A.toOver ⊗ A.toOver).left :=
    Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (A.toOver ⊗ A.toOver).hom
  constructor
  · apply schemeMap_ext
    intro x
    change (x ≫ MonObj.one) ≫ g = x ≫ MonObj.one
    have hxA : (x ≫ MonObj.one : Points A) = 1 := by
      rw [CategoryTheory.Hom.one_def]
      congr 1
      exact CartesianMonoidalCategory.toUnit_unique _ _
    have hxB : (x ≫ MonObj.one : Points B) = 1 := by
      rw [CategoryTheory.Hom.one_def]
      congr 1
      exact CartesianMonoidalCategory.toUnit_unique _ _
    rw [hxA, hxB]
    exact (hg 1).trans f.map_one
  · apply schemeMap_ext
    intro x
    let p : Points A := x ≫ CartesianMonoidalCategory.fst A.toOver A.toOver
    let q : Points A := x ≫ CartesianMonoidalCategory.snd A.toOver A.toOver
    have hleft : x ≫ MonObj.mul = p * q := by
      simp [p, q, CategoryTheory.Hom.mul_def,
        ← CartesianMonoidalCategory.comp_lift]
    change (x ≫ MonObj.mul) ≫ g =
      x ≫ (MonoidalCategory.tensorHom g g) ≫ MonObj.mul
    rw [hleft, hg']
    rw [f.map_mul, ← hg' p, ← hg' q]
    simp [p, q, CategoryTheory.Hom.mul_def,
      ← CartesianMonoidalCategory.comp_lift]

/-- For a homomorphism on complex points, the remaining algebraicity
obligation is precisely existence of an inducing morphism over ℂ. -/
theorem algebraic_realization_iff
    (f : Points A →* Points B) :
    (∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x) ↔
    (∃ g : A.toOver ⟶ B.toOver,
      ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x) := by
  constructor
  · rintro ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, isMonHom_of_map_eq f g hg, hg⟩

/-- A homomorphism with constant identity value is induced by the algebraic
identity section after the unique map to the base. -/
theorem algebraic_realization_of_eq_one (f : Points A →* Points B)
    (hf : ∀ x, f x = 1) :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
  let g : A.toOver ⟶ B.toOver :=
    CartesianMonoidalCategory.toUnit A.toOver ≫ MonObj.one
  have hg (x : Points A) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
    rw [hf x]
    change (x ≫ CartesianMonoidalCategory.toUnit A.toOver) ≫ MonObj.one = 1
    rw [CategoryTheory.Hom.one_def]
    congr 1
    exact CartesianMonoidalCategory.toUnit_unique _ _
  exact ⟨g, isMonHom_of_map_eq f g hg, hg⟩

theorem algebraic_realization_of_subsingleton_source (f : Points A →* Points B)
    [Subsingleton (Points A)] :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
  apply algebraic_realization_of_eq_one f
  intro x
  rw [Subsingleton.elim x 1, f.map_one]

theorem algebraic_realization_of_subsingleton_target (f : Points A →* Points B)
    [Subsingleton (Points B)] :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x :=
  algebraic_realization_of_eq_one f (fun _ => Subsingleton.elim _ _)

theorem subsingleton_projectiveSpace_zero :
    Subsingleton (Projectivization ℂ (Fin 1 → ℂ)) := by
  have hp (p : Projectivization ℂ (Fin 1 → ℂ)) :
      p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart (0 : Fin 1)).source := by
    obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source p
    have hi0 : i = (0 : Fin 1) := Fin.ext (by omega)
    simpa only [hi0] using hi
  constructor
  intro p q
  exact (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart (0 : Fin 1)).injOn (hp p) (hp q)
    (Subsingleton.elim _ _)

theorem subsingleton_points_of_ambientDimension_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (hA : A.variety.presentation.projective.ambientDimension = 0) :
    Subsingleton (Points A) := by
  have hP : Subsingleton (Projectivization ℂ (ProjectiveCoordinates A → ℂ)) := by
    change Subsingleton (Projectivization ℂ
      (Fin (A.variety.presentation.projective.ambientDimension + 1) → ℂ))
    rw [hA]
    exact subsingleton_projectiveSpace_zero
  exact (isClosedEmbedding_projectiveEmbedding A).injective.subsingleton

theorem algebraic_realization_of_ambientDimension_zero
    (f : Points A →* Points B)
    (h : A.variety.presentation.projective.ambientDimension = 0 ∨
      B.variety.presentation.projective.ambientDimension = 0) :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
  rcases h with hA | hB
  · let : Subsingleton (Points A) := subsingleton_points_of_ambientDimension_zero A hA
    exact algebraic_realization_of_subsingleton_source f
  · let : Subsingleton (Points B) := subsingleton_points_of_ambientDimension_zero B hB
    exact algebraic_realization_of_subsingleton_target f

/-- The inverse of the algebraic graph projection recovers the given
holomorphic map, and equality on complex points recovers its group law. -/
theorem algebraic_realization_of_holomorphic
    (f : Points A →* Points B)
    (hf : MDifferentiable (𝓘(ℂ, Model A)) (𝓘(ℂ, Model B)) (fun x => f x)) :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
  obtain ⟨Z, p, q, hZ, hproperZ, hp, hbij, hq⟩ := exists_proper_graph_projection f hf
  let : IsReduced Z.left := hZ
  let : IsProper Z.hom := hproperZ
  let : IsProper p.left := hp
  let : IsIso p.left := FiniteNormalIso.Constructions.Algebraization.isIso_of_proper_bijective_complex_points p hbij
  let : IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map p) := inferInstanceAs (IsIso p.left)
  let : IsIso p := isIso_of_reflects_iso p (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase)
  let g := inv p ≫ q
  have hg (x : Points A) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x := by
    rw [show g = inv p ≫ q from rfl, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hq]
    change f ((x ≫ inv p) ≫ p) = f x
    simp
  exact ⟨g, isMonHom_of_map_eq f g hg, hg⟩

end Constructions

namespace CM

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

/-- HolomorphicAlgebraicity: every holomorphic group homomorphism between complex abelian
varieties is induced by an algebraic group homomorphism. -/
theorem holomorphic_group_hom_is_algebraic
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (hf : MDifferentiable
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ))
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension B.toOver.hom) → ℂ))
      (fun x => f x)) :
    ∃ g : A.toOver ⟶ B.toOver,
      IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x :=
  Constructions.algebraic_realization_of_holomorphic f hf

end CM

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
