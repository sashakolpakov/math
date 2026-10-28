import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSum
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenSupported
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SupportedCoefficientComparison

/-! # Section Supported -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionSupported.Constructions

noncomputable section

/-! The local cycle-section formula as the actual relative class of the finite supported normalization divisor. -/

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

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphClasses.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGysin.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionProjectionSum.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorCommonProjection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

local instance : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (s : Γ(Y.left, ⊤)) (hsn : X.left.germToFunctionField ⊤ (g.left.appTop s) ≠ 0)

local notation "R" => OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hsn
local notation "O" => X.left.basicOpen (g.left.appTop s)

local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V W
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage P U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s)
local notation "vG" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s
local notation "hD" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSection_unitDomain d s g f hsn

variable (hU : ∀ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X (X.left.basicOpen (g.left.appTop s)),
    (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
  (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

local notation "hT" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions.graphSection_bound_baseImage P U a j hUJ s f K hb

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSum.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenSupported.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

def sectionSupportedCycle : Open.SupportedLift.Constructions.Map.SupportedCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  OpenSupported.Constructions.supportedOpenPrincipalCycle V W a g j hs d f U hUJ hcover vG R hD S K hT hU

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem forget_sectionSupportedCycle :
    Open.SupportedLift.Constructions.Map.forgetCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (sectionSupportedCycle V W a g j hs d f U hUJ hcover s hsn hU K hb) =
    OpenPrincipal.Constructions.openPrincipalCycle V W a R :=
  OpenSupported.Constructions.forget_supportedOpenPrincipalCycle V W a g j hs d f U hUJ hcover vG R hD S K hT hU

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem sectionSupportedGenerator_class (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    Open.SupportedLift.Constructions.Map.relativeGenerator V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (OpenSupported.Constructions.divisorSupportedSupport V W a g j hs d f U hUJ hcover vG R hD S K hT z (hU z)) =
    NormalizationAffine.SectionSum.Constructions.sectionDivisorImageClass V W a g j hs d f U hUJ hcover s hsn hU K hb z :=
  OpenSupported.Constructions.divisorSupportedSupport_class V W a g j hs d f U hUJ hcover vG R hD S K hT z (hU z)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem sectionSupportedCycle_class :
    letI : Nonempty O := GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
    letI : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (sectionSupportedCycle V W a g j hs d f U hUJ hcover s hsn hU K hb) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
      ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
        ((PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) •
        NormalizationAffine.SectionSum.Constructions.sectionDivisorImageClass V W a g j hs d f U hUJ hcover s hsn hU K hb z := by
  classical
  let : Nonempty O := GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  let : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  simp only [sectionSupportedCycle, OpenSupported.Constructions.supportedOpenPrincipalCycle, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro z _
  rw [Open.SupportedLift.Constructions.Map.relativeClassMap_single,
    sectionSupportedGenerator_class, smul_smul]

include hf hK in
theorem cycle_sectionCup_eq_supportedCycleClass :
    ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s) (GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      (Geometric.DimensionCycles.dimensionCodimension V W) 1 (BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (sectionSupportedCycle V W a g j hs d f U hUJ hcover s hsn hU K hb) := by
  exact (NormalizationAffine.SectionSum.Constructions.cycle_sectionCup_eq_order_imageCycle_sum V W a g j hs d f hf U hUJ hcover s hsn hU K hK hb).trans
    (sectionSupportedCycle_class V W a g j hs d f U hUJ hcover s hsn hU K hb).symm

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SupportedCoefficientComparison.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

include hf hK hs hcover hU hb in
theorem cycle_sectionCup_eq_normalizedPrincipalClass
    (hsource : ∀ C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1),
      (∃ x : U, x.val ∈ Set.range C.analyticInclusion) →
      ∀ y : (AmbientMap.Constructions.smoothNormalizationOver V W).left,
        (PrincipalBoundary.Constructions.fullAmbientMap V W).left y = IntersectionGeometry.supportPoint C.val → y ∈ Set.range a.left) :
    ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s) (GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      (Geometric.DimensionCycles.dimensionCodimension V W) 1 (BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
      (Open.SupportedLift.Constructions.restrictCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
        (Principal.Constructions.normalizedPrincipalCycle V W
          (OpenFunctionField.Constructions.originalFunction V W a (X.left.germToFunctionField ⊤ (g.left.appTop s)))
          (OpenFunctionField.Constructions.originalFunction_ne_zero V W a _ hsn))) := by
  exact (cycle_sectionCup_eq_supportedCycleClass V W a g j hs d f hf U hUJ hcover s hsn hU K hK hb).trans
    (SupportedCoefficientComparison.Constructions.supportedClass_eq_normalized V W a R hsn U S
      (sectionSupportedCycle V W a g j hs d f U hUJ hcover s hsn hU K hb)
      (forget_sectionSupportedCycle V W a g j hs d f U hUJ hcover s hsn hU K hb) hsource)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SectionSupported.Constructions
