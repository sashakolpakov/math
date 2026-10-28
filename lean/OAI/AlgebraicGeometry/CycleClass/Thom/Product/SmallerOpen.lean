import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Smaller Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions

noncomputable section

/-! Restriction by the actual product of a smaller ambient-open inclusion sends the original graph Thom class to the actual restricted graph Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpenCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ProductHomeomorphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SubsetHomeomorph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {L N E G F : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E L]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup F] [NormedSpace ℂ F] (U P : Opens N) (hP : P ≤ U)

local instance (priority := low) (V : Opens N) : ChartedSpace (G × F) (V × F) := prodChartedSpace G V F F

variable (i : L → U × F) (hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G × F) ω i)

def smallerGraph : GraphOpenImmersion.Constructions.graphSourceOpen i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) → P × F :=
  SmallerOpenCoordinates.Constructions.smallerProductHomeomorph U P hP ∘ GraphOpenImmersion.Constructions.restrictedBase i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P))

theorem smallerGraph_analytic : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G × F) ω (smallerGraph U P hP i hi) :=
  (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph_analytic (G := G) (F := F) U P hP).comp
    (GraphOpenImmersion.Constructions.restrictedBase_analytic i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)))

theorem smallerGraph_differential_injective
    (hii : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G × F) i x))
    (x : GraphOpenImmersion.Constructions.graphSourceOpen i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P))) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G × F) (smallerGraph U P hP i hi) x) :=
  AmbientInverse.Constructions.transported_differential_injective
    (GraphOpenImmersion.Constructions.restrictedBase i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P))) (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph U P hP)
    (GraphOpenImmersion.Constructions.restrictedBase_analytic i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)))
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) hii)
    (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph_analytic (G := G) (F := F) U P hP)
    (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph_symm_analytic (G := G) (F := F) U P hP) x

theorem smallerGraph_closedEmbedding (hc : Topology.IsClosedEmbedding i) :
    Topology.IsClosedEmbedding (smallerGraph U P hP i hi) :=
  (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph U P hP).isClosedEmbedding.comp
    (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) hc)

theorem smallerGraph_mapsTo : Set.MapsTo (SmallerOpenCoordinates.Constructions.smallerProductMap (F := F) U P hP)
    (Set.range (smallerGraph U P hP i hi))ᶜ (Set.range i)ᶜ :=
  Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph U P hP)

variable [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω L]
  [FiniteDimensional ℂ G] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N] [FiniteDimensional ℂ F]

local instance (V : Opens N) : MetrizableSpace V := V.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (V : Opens N) : IsManifold 𝓘(ℂ, G × F) ω (V × F) := Immersion.Constructions.productModel_isManifold

theorem smallerGraph_Thom_pullback
    (hii : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G × F) i x))
    (hc : Topology.IsClosedEmbedding i) (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E (G × F) = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SmallerOpenCoordinates.Constructions.smallerProductMap (F := F) U P hP)
      (smallerGraph_mapsTo U P hP i hi) (2 * p) (Degree.Constructions.ThomClass.complexThomClassInDegree i hi hii hc p hp) =
      Degree.Constructions.ThomClass.complexThomClassInDegree (smallerGraph U P hP i hi) (smallerGraph_analytic U P hP i hi)
        (smallerGraph_differential_injective U P hP i hi hii) (smallerGraph_closedEmbedding U P hP i hi hc) p hp := by
  exact Open.ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport (N := U × F) (N' := P × F) (G := G × F) (H := G × F)
    i hi (Open.ProductHomeomorphAnalytic.Constructions.productBaseOpen (Open.SubsetHomeomorph.Constructions.insideOpen U P)) (SmallerOpenCoordinates.Constructions.smallerProductHomeomorph U P hP) hii hc
    ((SmallerOpenCoordinates.Constructions.smallerProductHomeomorph_analytic (G := G) (F := F) U P hP).mdifferentiable (by simp))
    ((SmallerOpenCoordinates.Constructions.smallerProductHomeomorph_symm_analytic (G := G) (F := F) U P hP).mdifferentiable (by simp))
    (smallerGraph_analytic U P hP i hi) (smallerGraph_differential_injective U P hP i hi hii) p hp hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmallerOpen.Constructions
