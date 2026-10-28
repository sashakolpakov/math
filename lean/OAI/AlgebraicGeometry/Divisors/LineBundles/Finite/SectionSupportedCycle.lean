import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SectionCycleSum
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeImagePoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle

/-! # Section Supported Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupportedCycle.BundleCycles

noncomputable section

/-! The actual order-weighted prime-image sum is a finite dimension-graded cycle in the section intersection support. -/

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

local instance finiteSectionSupportedCycleMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteSectionSupportedCycleCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteSectionSupportedCycleManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

local instance finiteSectionSupportedCycleTopNonempty : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, Opens.mem_top _⟩⟩

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

include hs hcover hb hsn hU in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteSectionImagePoint_supported (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) :
    (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) ⁻¹'
      Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (irreducibleSetEquivPoints.symm
        (PrimeImagePoint.BundleCycles.finitePrimeImagePoint k p hp a ⟨z.val, z.property.1⟩ n hn).val)) ⊆ T := by
  rw [PrimeImagePoint.BundleCycles.finitePrimeImagePoint_support]
  rw [← SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion_range N
    (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))) U
    ((hU z).trans (FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen_target_regular k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))))]
  exact FiniteAffine.SectionCycleSum.BundleCycles.finiteSectionDivisorSupport_le k p hp a g j hs d f U hUJ hcover s hsn hU K hb z

def finiteSectionSupportedImagePoint (z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) : Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedPoint N U T n :=
  ⟨PrimeImagePoint.BundleCycles.finitePrimeImagePoint k p hp a ⟨z.val, z.property.1⟩ n hn,
    finiteSectionImagePoint_supported k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z⟩

def finiteSectionSupportedCycle : Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedCycle N U T n :=
  letI : Nonempty O := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  letI : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
    Finsupp.single (finiteSectionSupportedImagePoint k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn z)
      ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
        (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ))

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem finiteSectionSupportedCycle_forget :
    letI : Nonempty O := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
    letI : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
    Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedCycle_forget N U T n
      (finiteSectionSupportedCycle k p hp a g j hs d f U hUJ hcover s hsn hU K hb n hn) =
    ∑ z : CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O,
      Finsupp.single (PrimeImagePoint.BundleCycles.finitePrimeImagePoint k p hp a ⟨z.val, z.property.1⟩ n hn)
        ((X.left.ord (X.left.germToFunctionField ⊤ (g.left.appTop s)) z.val : ℚ) *
          (k.left.residueDegree (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)) := by
  classical
  let : Nonempty O := CycleClass.Thom.GlobalSectionUnitRepresentative.Constructions.basicOpen_nonempty X.left (g.left.appTop s) hsn
  let : Fintype (CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X O) := Fintype.ofFinite _
  simp only [finiteSectionSupportedCycle, map_sum, Scheme.OpenSupportedCycle.BundleCycles.schemeOpenSupportedCycle_forget,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, finiteSectionSupportedImagePoint]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupportedCycle.BundleCycles
