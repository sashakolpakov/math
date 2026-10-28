import OAI.AlgebraicGeometry.Divisors.LineBundles.ThomProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction

/-! # Regular Projection Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.RegularProjectionClass.BundleCycles

noncomputable section

/-! Projection compatibility for the actual regular-locus Thom class of
every algebraic integral support, including singular supports and codimension zero. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (F B : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace B] [ChartedSpace F B] [IsManifold 𝓘(ℂ, F) ω B] [MetrizableSpace B]

local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance : MetrizableSpace G := MetrizableSpace.subtype _
local instance (priority := low) : ChartedSpace (F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z)
    (B × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z)) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance (priority := low) : ChartedSpace (F × E) (B × G) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance : IsManifold 𝓘(ℂ, F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) ω
    (B × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z)) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold 𝓘(ℂ, F × E) ω (B × G) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

def schemeRegularProjectionThomClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (B × G))
      (Set.range (Prod.map (id : B → B) j))ᶜ (2 * p) :=
  CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree (Prod.map (id : B → B) j)
    (Projection.Immersion.BundleCycles.projectionImmersion_contMDiff j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω))
    (Projection.Immersion.BundleCycles.projectionImmersion_injective_mfderiv j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z))
    (Topology.IsClosedEmbedding.id.prodMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)) p
    ((Projection.Immersion.BundleCycles.projectionImmersion_codimension (F := F)).trans (SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp))

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeRegularProjectionThomClass_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Projection.NormalRestriction.BundleCycles.normalProductProjection B G)
      (Projection.NormalRestriction.BundleCycles.normalProductProjection_mapsTo j) (2 * p) (SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp) =
      schemeRegularProjectionThomClass X Z p hp F B :=
  ThomProjection.BundleCycles.complexThomClassInDegree_projection_pullback j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    p (SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.RegularProjectionClass.BundleCycles
