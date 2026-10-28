import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Base Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class

noncomputable section

/-! The actual parent cycle on an ambient open, presented as an image
support for the image-intersection cup and its actual graph projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Opens V.analyticSpace)

def baseImage : (NormalizationAffine.SectionSupport.Constructions.parentBaseSupport D U) → U := Subtype.val

theorem baseImage_range : Set.range (baseImage D U) = NormalizationAffine.SectionSupport.Constructions.parentBaseSupport D U := Subtype.range_coe

def baseImageCycleClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Set.range (baseImage D U))ᶜ (2 * p) :=
  Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of U) (congrArg Set.compl (baseImage_range D U).symm) rfl
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range D.analyticInclusion)ᶜ U (2 * p) D.rationalSupportedCycleClass)

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]
  {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (K : Set (Fin d → ℂ)) (hb : ∀ x, GenericFibers.Constructions.Open.openBase D a x ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K)

omit [IsOpenImmersion a.left] in
include hb in
theorem graph_bound_baseImage : Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f) ⊆ Set.range (baseImage D U) ×ˢ K := by
  rw [baseImage_range]
  exact OpenGraph.Constructions.Class.normalizationOpenGraph_bound D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

theorem polynomialGraph_project_baseImage (hf : Function.Surjective f) (hK : IsCompact K)
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (baseImage D U)) K hK
      (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f)) (graph_bound_baseImage D U a f K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f)
        (OpenGraph.Constructions.Class.normalizationOpenGraph_analytic D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
        (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U
          (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
        (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf) (p + d) (GenericFibers.Constructions.Open.openGraph_codimension D a d)) =
      baseImageCycleClass D U := by
  have h := PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_project_cycleClass D a U f hcover hf K hK hb
  have ht := Projection.TargetSupport.Constructions.projectAt_targetCast d (TopCat.of U) (NormalizationAffine.SectionSupport.Constructions.parentBaseSupport D U) (Set.range (baseImage D U))
    (baseImage_range D U).symm K hK (Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f))
    (OpenGraph.Constructions.Class.normalizationOpenGraph_bound D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb) (graph_bound_baseImage D U a f K hb)
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
    (Degree.Constructions.ThomClass.complexThomClassInDegree (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f)
      (OpenGraph.Constructions.Class.normalizationOpenGraph_analytic D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
      (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U
        (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
      (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf) (p + d) (GenericFibers.Constructions.Open.openGraph_codimension D a d))
  exact ht.symm.trans (congrArg (eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Aᶜ (2 * p)) (baseImage_range D U).symm)) h)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class
