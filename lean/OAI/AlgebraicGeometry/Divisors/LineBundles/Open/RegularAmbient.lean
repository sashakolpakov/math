import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.ThomOpenPullback
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Regular Ambient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularAmbient.BundleCycles

noncomputable section

section

/-! An actual open immersion induces an open holomorphic embedding of
the regular ambient neighborhoods, with bijective complex differential. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] (i : X ⟶ Y) [IsOpenImmersion i.left]
    (B : IrreducibleCloseds Y.left) [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B
local notation "GX" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X A
local notation "GY" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "EX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "EY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbient_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i)
    (GX : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (GY : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  intro x hx
  exact (Set.ext_iff.mp (SupportSquare.BundleCycles.openSupport_regularAmbientOpen i B) x).mp hx

def openRegularAmbientMap : GX → GY := (openRegularAmbient_mapsTo i B).restrict

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbientMap_val (x : GX) :
    (openRegularAmbientMap i B x).val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x.val := rfl

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbientMap_open : Topology.IsOpenEmbedding (openRegularAmbientMap i B) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).restrict
    (openRegularAmbient_mapsTo i B) (GX).isOpen

theorem openRegularAmbientMap_analytic (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, EX) 𝓘(ℂ, EY) r (openRegularAmbientMap i B) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff GY (openRegularAmbientMap i B) r).mp
  exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map i r).comp
    (contMDiff_subtype_val («U» := GX) (n := r))

theorem openRegularAmbientMap_differential (x : GX) :
    Function.Bijective (mfderiv 𝓘(ℂ, EX) 𝓘(ℂ, EY) (openRegularAmbientMap i B) x) := by
  have hv := (show ContMDiff 𝓘(ℂ, EX) 𝓘(ℂ, EX) 1
    (Subtype.val : GX → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) from contMDiff_subtype_val).mdifferentiableAt
      (x := x) one_ne_zero
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := EX) («F» := EY) GY (openRegularAmbientMap i B) x
  change mfderiv 𝓘(ℂ, EX) 𝓘(ℂ, EY) (openRegularAmbientMap i B) x =
    mfderiv 𝓘(ℂ, EX) 𝓘(ℂ, EY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ∘ (Subtype.val : GX → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) x at hd
  rw [mfderiv_comp x (((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map i 1) x.val).mdifferentiableAt one_ne_zero) hv,
    CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact (congrArg (fun L : EX →L[ℂ] EY => Function.Bijective L) hd).mpr
    (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective i x.val)

def openRegularAmbientTopMap : TopCat.of GX ⟶ TopCat.of GY :=
  PullbackImmersion.BundleCycles.openPullbackAmbientMap (openRegularAmbientMap i B) (openRegularAmbientMap_open i B)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbientTopMap_toAmbient :
    openRegularAmbientTopMap i B ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (GY : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) =
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (GX : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ≫
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i := by
  ext x
  rfl

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbientMap_supportRange :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X A) =
      openRegularAmbientMap i B ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B) := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_range, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_range,
    SupportSquare.BundleCycles.openSupportInclusion_pointRange]
  rfl

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem openRegularAmbientTopMap_mapsTo : Set.MapsTo (openRegularAmbientTopMap i B)
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X A))ᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B))ᶜ :=
  ThomOpenPullback.BundleCycles.openPullbackThom_mapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B) (openRegularAmbientMap i B)
    (openRegularAmbientMap_open i B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X A)
    (openRegularAmbientMap_supportRange i B)

end

/-! The actual regular-support Thom class restricts to the canonical
regular-support class of the reduced open inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (i : X ⟶ Y) [IsOpenImmersion i.left]
    (B : IrreducibleCloseds Y.left) [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B
local notation "GX" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X A
local notation "GY" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "EX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "EY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "ha" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver.BundleCycles.openRestrictedSupportOver_codimension i B p hp

local instance : MetrizableSpace GX := MetrizableSpace.subtype _
local instance : MetrizableSpace GY := MetrizableSpace.subtype _

include i hp in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [Nonempty ↥(SupportRestriction.BundleCycles.openSupportPullback (Over.Hom.left i) B)] in
theorem openRegularSupport_mixedCodimension :
    CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) EX = p := by
  have h := Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension Y B p hp
  change Module.finrank ℂ EX - Module.finrank ℂ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) = p
  change Module.finrank ℂ EY - Module.finrank ℂ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) = p at h
  simpa only [Module.finrank_fin_fun, SupportSquare.BundleCycles.openImmersionOver_modelDimension i] using h

omit [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeRegularSupportThomClass_openPullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (openRegularAmbientTopMap i B)
      (openRegularAmbientTopMap_mapsTo i B) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass Y B p hp) = Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X A p ha := by
  exact ThomOpenPullback.BundleCycles.complexThomClassInDegree_openPullback
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff Y B ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed Y B)
    (openRegularAmbientMap i B) (openRegularAmbientMap_open i B)
    (openRegularAmbientMap_analytic i B ω) (openRegularAmbientMap_differential i B)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X A) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X A ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X A) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X A)
    (openRegularAmbientMap_supportRange i B)
    (SupportSquare.BundleCycles.openRestrictedRegularModelCoordinates i B) (SupportSquare.BundleCycles.openRestrictedRegularModelCoordinates_norm i B)
    p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension Y B p hp) (openRegularSupport_mixedCodimension i B p hp)
    (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X A p ha)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularAmbient.BundleCycles
