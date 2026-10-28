import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.IntersectionProjectionSum
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GraphSectionCup

/-! # Section Cycle Sum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionCycleSum.BundleCycles

noncomputable section

/-! The canonical finite-image cycle cup a genuine section class is the source-order and residue-degree weighted divisor image sum. Unit and equation data come from the actual section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.AmbientImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GysinAmbient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.AmbientInverse.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hs : a ≫ k = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (hf : Function.Surjective f)
  [IsClosedImmersion (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local instance finiteAffineSectionCycleSumMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteAffineSectionCycleSumCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteAffineSectionCycleSumManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

local instance finiteSectionCycleSumTopNonempty : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

variable (s : Γ(Y.left, ⊤)) (hsn : X.left.germToFunctionField ⊤ (g.left.appTop s) ≠ 0)

local notation "R" => OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.sectionUnitRepresentative X.left (g.left.appTop s) hsn
local notation "O" => X.left.basicOpen (g.left.appTop s)

local notation "T" => Set.range (OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport.BundleCycles.finiteBaseSectionImage j U hUJ s)
local notation "vG" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s
local notation "hD" => OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSection_unitDomain d s g f hsn

variable (hU : ∀ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X (X.left.basicOpen (g.left.appTop s)),
    (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
  (K : Set (Fin d → ℂ)) (hK : IsCompact K)
  (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
    CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K)

local notation "hT" => OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GraphSectionCup.BundleCycles.finiteGraphSection_bound_baseImage k U a j hUJ s f K hb

include hp hs hcover hb hsn in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteSectionDivisorSupport_le (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      ((hU z).trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))) ⊆ T := by
  have hu : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ⁻¹' (Set.range vG)ᶜ ⊆
      (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X O : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSection_unitDomain d s g f hsn
  have ht : Set.range (Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f) ∩
      Set.range (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntersectionSupport.BundleCycles.finiteIntersectionCoordinateMap j d U hUJ) vG) ⊆ T ×ˢ K :=
    Finite.GraphSectionCup.BundleCycles.finiteGraphSection_bound_baseImage k U a j hUJ s f K hb
  exact DivisorCommonProjection.BundleCycles.finiteDivisorImage_le_commonSupport k p hp a g j hs d f U hUJ hcover vG O z hu (hU z) T K ht

def finiteSectionDivisorImageClass (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Tᶜ (2 * (p + 1)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (A := Tᶜ)
    (B := (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
      ((hU z).trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))))ᶜ)
    (fun _ hx hy => hx (finiteSectionDivisorSupport_le k p hp a g j hs d f U hUJ hcover s hsn hU K hb z hy))
    (2 * (p + 1))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
        ((hU z).trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))))
      (2 * (p + 1))
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) (p + 1) (GraphDimension.BundleCycles.finitePrimeImage_dimension k p hp (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))

include hf hK in
theorem finiteCycle_sectionCup_eq_order_imageCycle_sum :
    letI : Nonempty (X.left.basicOpen (g.left.appTop s)) := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
    letI : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) (Finite.SectionSupport.BundleCycles.finiteBaseSectionImage j U hUJ s) (Finite.BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      (p) 1 (((k.left.residueDegree (genericPoint S.left) : ℚ) • Finite.BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U)) (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
      ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
        (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) •
        finiteSectionDivisorImageClass k p hp a g j hs d f U hUJ hcover s hsn hU K hb z := by
  classical
  let : Nonempty (X.left.basicOpen (g.left.appTop s)) := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  let : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  have hsum := IntersectionProjectionSum.BundleCycles.finiteGraphIntersection_project_order_imageCycle_sum k p hp a g j hs d f hf U hUJ hcover
    vG (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s) R hsn hD hU
    (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionEquation Y d s) (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionEquation_mapsTo Y d s) (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSection_unitEvaluation d s g f hsn)
    T K hK hb hT
  have hc := Finite.GraphSectionCup.BundleCycles.finiteGraphSectionCup_project k p hp U a j hUJ s f K hb hf hK hcover
  have h := hc.symm.trans hsum
  change _ = ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
    (X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) •
      ((k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ) •
        finiteSectionDivisorImageClass k p hp a g j hs d f U hUJ hcover s hsn hU K hb z) at h
  simpa only [smul_smul] using h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionCycleSum.BundleCycles
