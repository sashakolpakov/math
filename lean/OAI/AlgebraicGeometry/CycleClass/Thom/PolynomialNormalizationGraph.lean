import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic

/-! # Polynomial Normalization Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class

noncomputable section

/-! An actual surjective polynomial presentation supplies every immersion hypothesis for the normalization graph projection formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]
  (U : Opens V.analyticSpace)
  {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

abbrev polynomialNormalizationGraph := Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f)

omit [IsOpenImmersion a.left] in
theorem polynomialNormalizationGraph_closed (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (polynomialNormalizationGraph D a U f) :=
  GraphBaseRestriction.Constructions.restrictedGraph_closedEmbedding (Normalization.GenericFibers.Constructions.Open.openBase D a) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) U
    (Closed.GraphEmbedding.Constructions.graph_closedEmbedding (Normalization.GenericFibers.Constructions.Open.openBase D a) (Normalization.GenericFibers.Constructions.Open.openBase_analytic D a).continuous
      (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf))

theorem polynomialNormalizationGraph_project_cycleClass
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))
    (hf : Function.Surjective f) (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hb : ∀ x, Normalization.GenericFibers.Constructions.Open.openBase D a x ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion)
      K hK (Set.range (polynomialNormalizationGraph D a U f))
      (Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph_bound D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (polynomialNormalizationGraph D a U f)
        (Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph_analytic D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
        (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (Normalization.GenericFibers.Constructions.Open.openBase D a) (Normalization.GenericFibers.Constructions.Open.openBase_analytic D a) U
          (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
        (polynomialNormalizationGraph_closed D a U f hf) (p + d) (Normalization.GenericFibers.Constructions.Open.openGraph_codimension D a d)) =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass :=
  Normalization.OpenGraph.Constructions.Class.normalizationOpenGraph_project_cycleClass D a U hcover (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f)
    (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf) (polynomialNormalizationGraph_closed D a U f hf) K hK hb

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class
