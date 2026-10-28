import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Open Supported -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenSupported.Constructions

noncomputable section

/-! The actual finite normalization divisor is lifted to the common analytic support, preserving its original cycle coefficients and supported classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
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

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorComplement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

variable {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))
  {r : X.left.functionField} (R : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left r)
  (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range v)ᶜ ⊆
    (Scheme.SectionEvaluation.Constructions.analyticOpen X R.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
  (S : Set U) (K : Set (Fin d → ℂ))
  (hT : Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (ParentGraphImage.Constructions.supportCycle V W) a U f) ∩
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (NormalizationAffine.IntersectionSupport.Constructions.coordinateMap V j d U hUJ) v) ⊆ S ×ˢ K)

section Single
variable (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R.domain)
  (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))

def divisorSupportedSupport : Open.SupportedLift.Constructions.Map.SupportedSupport V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  ⟨NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩), by
    rw [← Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_range (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))]
    exact NormalizationAffine.DivisorCommonProjection.Constructions.divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v R.domain z hR hU S K hT⟩

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem divisorSupportedSupport_class :
    Open.SupportedLift.Constructions.Map.relativeGenerator V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (divisorSupportedSupport V W a g j hs d f U hUJ hcover v R hR S K hT z hU) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (A := Sᶜ)
      (B := (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
        (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))ᶜ)
      (fun _ hx hy => hx (NormalizationAffine.DivisorCommonProjection.Constructions.divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v R.domain z hR hU S K hT hy))
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
        (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
          (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))
        (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
        (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).rationalSupportedCycleClass) := by
  exact (ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (A := Sᶜ)
      (B := (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
        (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))ᶜ)
      (fun _ hx hy => hx (NormalizationAffine.DivisorCommonProjection.Constructions.divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover v R.domain z hR hU S K hT hy))
      (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
        (hU.trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)))
    (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).rationalSupportedCycleClass).symm
end Single

variable (hU : ∀ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R.domain,
  (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R.domain) := Fintype.ofFinite _

def supportedOpenPrincipalCycle : Open.SupportedLift.Constructions.Map.SupportedCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R.domain, (X.left.ord r z.val : ℚ) •
    Finsupp.single (divisorSupportedSupport V W a g j hs d f U hUJ hcover v R hR S K hT z (hU z))
      ((PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem forget_supportedOpenPrincipalCycle :
    Open.SupportedLift.Constructions.Map.forgetCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (supportedOpenPrincipalCycle V W a g j hs d f U hUJ hcover v R hR S K hT hU) = OpenPrincipal.Constructions.openPrincipalCycle V W a R := by
  classical
  simp only [supportedOpenPrincipalCycle, OpenPrincipal.Constructions.openPrincipalCycle, map_sum, map_smul,
    Open.SupportedLift.Constructions.Map.forgetCycle, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenSupported.Constructions
