import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.IntersectionProjectionSum
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup

/-! # Section Sum -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSum.Constructions

noncomputable section

/-! Local supported cycle-section compatibility for the singular parent cycle: the actual parent cycle cup is the sum of the original divisor image-cycle classes with literal source orders and normalization residue degrees. Equation and unit data are constructed from the actual regular section. -/

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

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
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
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

local notation "hT" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions.graphSection_bound_baseImage P U a j hUJ s f K hb

include hs hcover hb hsn in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem sectionDivisorSupport_le (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      ((hU z).trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))) ⊆ S := by
  have hu : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range vG)ᶜ ⊆
      (Scheme.SectionEvaluation.Constructions.analyticOpen X O : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := Affine.GraphSectionEquation.Constructions.graphSection_unitDomain d s g f hsn
  have ht : Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph P a U f) ∩
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.Constructions.coordinateMap V j d U hUJ) vG) ⊆ S ×ˢ K :=
    Normalization.GraphSectionCup.Constructions.graphSection_bound_baseImage P U a j hUJ s f K hb
  exact DivisorCommonProjection.Constructions.divisorImage_le_commonSupport V W a g j hs d f U hUJ hcover vG O z hu (hU z) S K ht

def sectionDivisorImageClass (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Sᶜ (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (A := Sᶜ)
    (B := (Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
      ((hU z).trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))ᶜ)
    (fun _ hx hy => hx (sectionDivisorSupport_le V W a g j hs d f U hUJ hcover s hsn hU K hb z hy))
    (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)) U
        ((hU z).trans (NormalizationDivisor.GraphOpen.Constructions.goodAmbient_regular V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))
      (2 * (Geometric.DimensionCycles.dimensionCodimension V W + 1))
      (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).rationalSupportedCycleClass)

include hf hK in
theorem cycle_sectionCup_eq_order_imageCycle_sum :
    letI : Nonempty (X.left.basicOpen (g.left.appTop s)) := GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
    letI : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
    ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage P U) (SectionSupport.Constructions.baseSectionImage j U hUJ s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      (Geometric.DimensionCycles.dimensionCodimension V W) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
      ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
        ((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) •
        sectionDivisorImageClass V W a g j hs d f U hUJ hcover s hsn hU K hb z := by
  classical
  let : Nonempty (X.left.basicOpen (g.left.appTop s)) := GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  let : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  have hsum := IntersectionProjectionSum.Constructions.graphIntersection_project_order_imageCycle_sum V W a g j hs d f hf U hUJ hcover
    vG (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s) R hsn hD hU
    (Affine.GraphSectionEquation.Constructions.graphSectionEquation Y d s) (Affine.GraphSectionEquation.Constructions.graphSectionEquation_mapsTo Y d s) (Affine.GraphSectionEquation.Constructions.graphSection_unitEvaluation d s g f hsn)
    S K hK hb hT
  have hc := Normalization.GraphSectionCup.Constructions.graphSectionCup_project P U a j hUJ s f K hb hf hK hcover
  have h := hc.symm.trans hsum
  change _ = ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
    (X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) •
      (((Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ) •
        sectionDivisorImageClass V W a g j hs d f U hUJ hcover s hsn hU K hb z) at h
  simpa only [smul_smul] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSum.Constructions
