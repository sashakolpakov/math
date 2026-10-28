import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed

/-! # Affine Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraph.Constructions.Class

noncomputable section

/-! The actual polynomial normalization divisor graphs project to their original ambient cycle classes with the exact residue degree. Holomorphy, closedness, fiber multiplicity, and source dimension are derived from the construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.LocalGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ GraphOpen.Constructions.goodAmbient V W z)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V W + 1

variable {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ) × (Fin d → ℂ)) ω
    (U × (Fin d → ℂ)) := Product.Immersion.Constructions.productModel_isManifold

theorem affineDivisorGraph_project_imageCycleClass (hf : Function.Surjective f)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
      Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U)
      (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z)))) K hK
      (Set.range (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f)))
      (LocalGraph.Constructions.Class.divisorLocalGraph_bound V W z U hU (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f) K
        (AffineCoordinates.Constructions.coverAffineCoordinates_bound V W z U a hcover f K hb))
      (2 * q) (2 * (q + d)) (Nat.mul_add 2 q d).symm
      (Degree.Constructions.ThomClass.complexThomClassInDegree
        (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f))
        (EtaleLocalGraph.Constructions.localGraph_analytic (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
          (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f) (AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W z U a hcover f))
        (EtaleLocalGraph.Constructions.localGraph_differential_injective (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
          (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f) (AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W z U a hcover f))
        (AffineGraphClosed.Constructions.coverAffineGraph_closedEmbedding V W z a f U hcover hU hf) (q + d) (GraphOpen.Constructions.sourceGraph_codimension V W z d)) =
      ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val : ℚ) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
          (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (Image.Constructions.imageCycleSupport V W z) U (hU.trans (GraphOpen.Constructions.goodAmbient_regular V W z))) (2 * q)
          (Image.Constructions.imageCycleSupport V W z).rationalSupportedCycleClass :=
  LocalGraph.Constructions.Class.divisorLocalGraph_project_imageCycleClass V W z U hU (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f) K
    (AffineCoordinates.Constructions.coverAffineCoordinates_analytic V W z U a hcover f)
    (AffineGraphClosed.Constructions.coverAffineGraph_closedEmbedding V W z a f U hcover hU hf) hK
    (AffineCoordinates.Constructions.coverAffineCoordinates_bound V W z U a hcover f K hb)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraph.Constructions.Class
