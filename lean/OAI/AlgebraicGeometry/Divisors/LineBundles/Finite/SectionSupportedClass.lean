import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedGeneratorComparison

/-! # Section Supported Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupportedClass.BundleCycles

noncomputable section

/-! The local section cup is exactly the canonical supported class of the actual finite order and residue-degree weighted image cycle. -/

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

local instance finiteSectionSupportedClassMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteSectionSupportedClassCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteSectionSupportedClassManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

local instance finiteSectionSupportedClassTopNonempty : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

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

variable (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteSectionSupportedImagePoint_generator (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeGenerator N U T n (p + 1) hn
      (SectionSupportedCycle.BundleCycles.finiteSectionSupportedImagePoint k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z) =
      FiniteAffine.SectionCycleSum.BundleCycles.finiteSectionDivisorImageClass k p hp a g j hs d f U hUJ hcover s hsn hU K hb z := by
  let C := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
  have hpC := FiniteAffine.GraphDimension.BundleCycles.finitePrimeImage_dimension k p hp (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)
  let hr := (hU z).trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)))
  let hm : Set.MapsTo (𝟙 (TopCat.of U)) Tᶜ (Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N C U hr))ᶜ :=
    fun _ hx hy => hx (FiniteAffine.SectionCycleSum.BundleCycles.finiteSectionDivisorSupport_le k p hp a g j hs d f U hUJ hcover s hsn hU K hb z hy)
  let hj := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hj
      hm (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo N C U hr) (2 * (p + 1)))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N C (p + 1) hpC)
  simp only [Category.id_comp] at hc
  have hg := Scheme.SupportedGeneratorComparison.BundleCycles.schemeOpenRelativeGenerator_of_support_eq N U T n (p + 1) hn
    (SectionSupportedCycle.BundleCycles.finiteSectionSupportedImagePoint k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z) C hpC
    (PrimeImagePoint.BundleCycles.finitePrimeImagePoint_support k p hp a ⟨z.val, z.property.1⟩ n hn)
    ((SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_mapsTo N C U hr).comp hm)
  exact hg.trans hc.symm

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteSectionSupportedCycle_class :
    letI : Nonempty O := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
    letI : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
    Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U T n (p + 1) hn
      (SectionSupportedCycle.BundleCycles.finiteSectionSupportedCycle k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn) =
    ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
      ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
        (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) •
        FiniteAffine.SectionCycleSum.BundleCycles.finiteSectionDivisorImageClass k p hp a g j hs d f U hUJ hcover s hsn hU K hb z := by
  classical
  let : Nonempty O := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  let : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  simp only [SectionSupportedCycle.BundleCycles.finiteSectionSupportedCycle, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  have h := Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap_single N U T n (p + 1) hn
    (SectionSupportedCycle.BundleCycles.finiteSectionSupportedImagePoint k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z)
    ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
      (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ))
  exact h.trans (congrArg (fun b =>
    ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
      (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) • b)
    (finiteSectionSupportedImagePoint_generator k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z))

include hf hK in
theorem finiteCycle_sectionCup_eq_supportedCycle :
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImageClass.BundleCycles.finiteBaseImage k U) (SectionSupport.BundleCycles.finiteBaseSectionImage j U hUJ s) (BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      p 1 ((k.left.residueDegree (genericPoint S.left) : ℚ) • BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U)
      (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeOpenRelativeClassMap N U T n (p + 1) hn
      (SectionSupportedCycle.BundleCycles.finiteSectionSupportedCycle k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn) := by
  exact (FiniteAffine.SectionCycleSum.BundleCycles.finiteCycle_sectionCup_eq_order_imageCycle_sum k p hp a g j hs d f hf U hUJ hcover s hsn hU K hK hb).trans
    (finiteSectionSupportedCycle_class k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupportedClass.BundleCycles
