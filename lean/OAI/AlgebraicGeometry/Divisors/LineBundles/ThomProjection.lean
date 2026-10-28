import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.Immersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.CenteredManifoldChart
import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality

/-! # Thom Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ThomProjection.BundleCycles

noncomputable section

/-! The genuine supported Thom class commutes with projection pullback.
The proof constructs normal neighborhoods at every source point and uses
the uniqueness theorem for the actual complex Thom class. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open scoped _root_.Manifold ContDiff

variable {E F G M B N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ, F) ω B] [MetrizableSpace B]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℂ, G) ω N] [MetrizableSpace N]

local instance (priority := low) : ChartedSpace (F × E) (B × M) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted F B E M
local instance (priority := low) : ChartedSpace (F × G) (B × N) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted F B G N
local instance : IsManifold 𝓘(ℂ, F × E) ω (B × M) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold 𝓘(ℂ, F × G) ω (B × N) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
local instance : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F

variable (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω u)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) u x))
    (he : Topology.IsClosedEmbedding u)

theorem complexThomClass_projection_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Projection.NormalRestriction.BundleCycles.normalProductProjection B N)
      (Projection.NormalRestriction.BundleCycles.normalProductProjection_mapsTo u) (2 * CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G)
      (CycleClass.Geometric.ComplexThom.Cycles.complexThomClass u hu hi he) =
    CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map (id : B → B) u)
      (Projection.Immersion.BundleCycles.projectionImmersion_contMDiff u hu) (Projection.Immersion.BundleCycles.projectionImmersion_injective_mfderiv u hu hi)
      (Topology.IsClosedEmbedding.id.prodMap he) (CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G)
      (Projection.Immersion.BundleCycles.projectionImmersion_codimension (F := F)) := by
  let P := CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionNormalPair u hu hi he
  let c := CenteredManifoldChart.BundleCycles.centeredManifoldChart F B
  let hb := CenteredManifoldChart.BundleCycles.centeredManifoldChart_source F B
  let hc := CenteredManifoldChart.BundleCycles.centeredManifoldChart_point F B
  let Q := fun z : B × M => Projection.NormalPair.BundleCycles.projectionNormalPair (P z.2) (c z.1) z.1 (hb z.1) (hc z.1)
  have hQ : ∀ z, (Q z).ambientChart.MDifferentiable
      𝓘(ℂ, F × G) 𝓘(ℂ, (F × E) × (Fin (CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G) → ℂ)) := by
    intro z
    rw [modelWithCornersSelf_prod]
    exact Projection.NormalClass.BundleCycles.projectionNormalPair_mdifferentiable (P z.2) (c z.1) z.1 (hb z.1) (hc z.1)
      (CenteredManifoldChart.BundleCycles.centeredManifoldChart_mdifferentiable F B z.1)
      (CycleClass.Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable u hu hi he z.2)
  apply CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree_unique (Prod.map (id : B → B) u)
    (Projection.Immersion.BundleCycles.projectionImmersion_contMDiff u hu) (Projection.Immersion.BundleCycles.projectionImmersion_injective_mfderiv u hu hi)
    (Topology.IsClosedEmbedding.id.prodMap he) (CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G)
    (Projection.Immersion.BundleCycles.projectionImmersion_codimension (F := F)) Q hQ
  intro z
  have h := Projection.NormalRestriction.BundleCycles.projectionNormalPair_restriction (P z.2) (c z.1) z.1 (hb z.1) (hc z.1)
    (CycleClass.Geometric.ComplexThom.Cycles.complexThomClass u hu hi he)
  have hP : CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ
      (P z.2).openNeighborhood (2 * CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G)
      (CycleClass.Geometric.ComplexThom.Cycles.complexThomClass u hu hi he) = (P z.2).rationalClassFin :=
    CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree_restrict u hu hi he (CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G) rfl z.2
      (P z.2) (CycleClass.Geometric.ComplexThom.Cycles.complexImmersionNormalPair_mdifferentiable u hu hi he z.2)
  exact h.trans ((congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Projection.NormalClass.BundleCycles.projectionNormalPairToBase (P z.2) (c z.1) z.1 (hb z.1) (hc z.1))
      (Projection.NormalClass.BundleCycles.projectionNormalPairToBase_mapsTo (P z.2) (c z.1) z.1 (hb z.1) (hc z.1))
      (2 * CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G)) hP).trans
        (Projection.NormalClass.BundleCycles.projectionNormalPair_class (P z.2) (c z.1) z.1 (hb z.1) (hc z.1)))

theorem complexThomClassInDegree_projection_pullback (p : ℕ)
    (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Projection.NormalRestriction.BundleCycles.normalProductProjection B N)
      (Projection.NormalRestriction.BundleCycles.normalProductProjection_mapsTo u) (2 * p) (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi he p hp) =
    CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map (id : B → B) u)
      (Projection.Immersion.BundleCycles.projectionImmersion_contMDiff u hu) (Projection.Immersion.BundleCycles.projectionImmersion_injective_mfderiv u hu hi)
      (Topology.IsClosedEmbedding.id.prodMap he) p
      ((Projection.Immersion.BundleCycles.projectionImmersion_codimension (F := F)).trans hp) := by
  subst p
  exact complexThomClass_projection_pullback u hu hi he

theorem complexThomClassInDegree_projection_absolute (p : ℕ)
    (hp : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E G = p) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (Projection.NormalRestriction.BundleCycles.normalProductProjection B N) (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p)
        (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi he p hp)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (B × N))
      (Set.range (Prod.map (id : B → B) u))ᶜ (2 * p)
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map (id : B → B) u)
        (Projection.Immersion.BundleCycles.projectionImmersion_contMDiff u hu) (Projection.Immersion.BundleCycles.projectionImmersion_injective_mfderiv u hu hi)
        (Topology.IsClosedEmbedding.id.prodMap he) p
        ((Projection.Immersion.BundleCycles.projectionImmersion_codimension (F := F)).trans hp)) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (Projection.NormalRestriction.BundleCycles.normalProductProjection B N)
      (Projection.NormalRestriction.BundleCycles.normalProductProjection_mapsTo u) (2 * p)) (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi he p hp)
  exact h.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (B × N))
      (Set.range (Prod.map (id : B → B) u))ᶜ (2 * p))
    (complexThomClassInDegree_projection_pullback u hu hi he p hp))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ThomProjection.BundleCycles
