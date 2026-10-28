import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularAnalytic
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularModels
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.RegularProjectionClass
import OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare

/-! # Regular To -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularTo.BundleCycles

noncomputable section

section

/-! The genuine projection-support Thom class is the transported product
Thom class on its entire regular ambient neighborhood. Every geometric
and dimension input is supplied by the actual product construction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions
open scoped _root_.Manifold ContDiff

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (B : IrreducibleCloseds Y.left) (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)]
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY))
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "F" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "K" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.hom) → ℂ
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C
local notation "H" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Z C
local notation "k" => Prod.map (id : OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B)
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles.projectionRegularAmbientHomeomorph X Y B Z πX πY hprod
local notation "r" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles.projectionRegularPointsHomeomorph X Y B Z πX πY hprod
local notation "hc" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension X Y B Z πX πY hprod p hp

local instance : MetrizableSpace G := MetrizableSpace.subtype _
local instance : MetrizableSpace H := MetrizableSpace.subtype _
local instance (priority := low) : ChartedSpace (F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B)) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance (priority := low) : ChartedSpace (F × E) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) := CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance : IsManifold 𝓘(ℂ, F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) ω
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B)) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold 𝓘(ℂ, F × E) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) := CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem projectionRegularThom_commutes : e ∘ j = k ∘ r :=
  funext (RegularInv.BundleCycles.projectionRegularAmbientHomeomorph_inclusion X Y B Z πX πY hprod)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem projectionRegularThom_mapsTo : Set.MapsTo (CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (Set.range j)ᶜ (Set.range k)ᶜ :=
  CycleClass.Thom.CommutingSquare.Constructions.squareMapsTo j k e r (r).surjective (projectionRegularThom_commutes X Y B Z πX πY hprod)

include hp in
omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem projectionRegularThom_mixedCodimension : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Z C) (F × E) = p := by
  have hdim := RegularModels.BundleCycles.projectionRegularModel_dimension X Y B Z πX πY hprod
  have hb : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B).hom + p =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
    rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq]
    exact hp.trans (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom)
  change Module.finrank ℂ (F × E) - Module.finrank ℂ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Z C) = p
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  omega

omit [AlgebraicGeometry.IsNoetherian Y.left] [AlgebraicGeometry.IsNoetherian Z.left] in
theorem projectionRegularThom_transport :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (projectionRegularThom_mapsTo X Y B Z πX πY hprod) (2 * p)
      (Scheme.RegularProjectionClass.BundleCycles.schemeRegularProjectionThomClass Y B p hp F (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) =
      Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass Z C p hc := by
  have he : ContMDiff 𝓘(ℂ, K) 𝓘(ℂ, F × E) ω e := by
    rw [modelWithCornersSelf_prod]
    exact RegularAnalytic.BundleCycles.projectionRegularAmbientHomeomorph_contMDiff X Y B Z πX πY hprod ω
  have hei : MDifferentiable 𝓘(ℂ, F × E) 𝓘(ℂ, K) (e).symm := by
    rw [modelWithCornersSelf_prod]
    exact (RegularAnalytic.BundleCycles.projectionRegularAmbientHomeomorph_symm_contMDiff X Y B Z πX πY hprod ω).mdifferentiable (by simp)
  exact CycleClass.Thom.CommutingSquare.Constructions.complexThomClassInDegree_commutingSquare j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff Z C ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective Z C) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed Z C)
    k (Immersion.BundleCycles.projectionImmersion_contMDiff (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff Y B ω))
    (Immersion.BundleCycles.projectionImmersion_injective_mfderiv (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff Y B ω) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective Y B))
    (Topology.IsClosedEmbedding.id.prodMap (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed Y B))
    e he hei r (r).surjective (projectionRegularThom_commutes X Y B Z πX πY hprod)
    (RegularModels.BundleCycles.projectionRegularModelCoordinates X Y B Z πX πY hprod)
    (RegularModels.BundleCycles.projectionRegularModelCoordinates_norm X Y B Z πX πY hprod)
    p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension Z C p hc)
    ((show CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (F × CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) (F × E) =
      CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel Y B) E from Immersion.BundleCycles.projectionImmersion_codimension).trans
        (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension Y B p hp))
    (projectionRegularThom_mixedCodimension X Y B Z πX πY hprod p hp)

end

section

/-! Pullback along the literal restricted scheme projection carries the
base regular-support Thom class to the inverse-image regular-support class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (B : IrreducibleCloseds Y.left) (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)]
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY))

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C
local notation "H" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles.projectionRegularAmbientHomeomorph X Y B Z πX πY hprod

def projectionRegularBaseMap : TopCat.of G ⟶ TopCat.of H :=
  CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap e ≫ NormalRestriction.BundleCycles.normalProductProjection (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) H

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem projectionRegularBaseMap_mapsTo : Set.MapsTo (projectionRegularBaseMap X Y B Z πX πY hprod)
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Z C))ᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B))ᶜ :=
  (NormalRestriction.BundleCycles.normalProductProjection_mapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B)).comp
    (projectionRegularThom_mapsTo X Y B Z πX πY hprod)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem projectionRegularBaseMap_toAmbient :
    projectionRegularBaseMap X Y B Z πX πY hprod ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (H : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) =
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)) (G : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)) ≫
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY := by
  ext z
  rfl

omit [AlgebraicGeometry.IsNoetherian Y.left] [AlgebraicGeometry.IsNoetherian Z.left] in
theorem schemeRegularSupportThomClass_projection (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (projectionRegularBaseMap X Y B Z πX πY hprod)
      (projectionRegularBaseMap_mapsTo X Y B Z πX πY hprod) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass Y B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass Z C p (SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension X Y B Z πX πY hprod p hp) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp (ModuleCat.of ℚ ℚ) (CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (NormalRestriction.BundleCycles.normalProductProjection (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) H) (projectionRegularThom_mapsTo X Y B Z πX πY hprod)
      (NormalRestriction.BundleCycles.normalProductProjection_mapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B)) (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass Y B p hp)
  have hc := congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (projectionRegularThom_mapsTo X Y B Z πX πY hprod) (2 * p))
    (Scheme.RegularProjectionClass.BundleCycles.schemeRegularProjectionThomClass_pullback Y B p hp
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  exact h.trans (hc.trans (projectionRegularThom_transport X Y B Z πX πY hprod p hp))

end

/-! The canonical supported class of every integral closed support pulls
back under an actual product projection to the canonical supported class
of its full reduced inverse image, including singular supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (B : IrreducibleCloseds Y.left) (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)]
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY))

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C
local notation "H" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "TZ" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)
local notation "TY" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
local notation "SZ" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Z C))ᶜ
local notation "SY" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B))ᶜ
local notation "JZ" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Z C))ᶜ
local notation "JY" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B))ᶜ

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsIntegral Z.left] [Smooth Z.hom] [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)] in
theorem schemeProjection_support_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY) SZ SY := by
  intro z hz hy
  apply hz
  exact (Set.ext_iff.mp (RegularInv.BundleCycles.projectionSupportInclusion_range X Y B Z πX πY hprod) z).mpr hy

theorem schemeSupportedCycleClass_projection (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY)
      (schemeProjection_support_mapsTo X Y B Z πX πY hprod) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Z C p (SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension X Y B Z πX πY hprod p hp) := by
  apply Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_unique Z C p (SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension X Y B Z πX πY hprod p hp)
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion TZ (G : Set TZ)
  let g := projectionRegularBaseMap X Y B Z πX πY hprod
  have hj : Set.MapsTo j JZ SZ :=
    CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo TZ SZ G JZ (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq Z C)
  have hg : Set.MapsTo g JZ JY := projectionRegularBaseMap_mapsTo X Y B Z πX πY hprod
  have hy : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion TY (H : Set TY)) JY SY :=
    CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo TY SY H JY (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq Y B)
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY)
      hj (schemeProjection_support_mapsTo X Y B Z πX πY hprod) (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have h₂ := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
      (projectionRegularBaseMap_toAmbient X Y B Z πX πY hprod).symm
      ((schemeProjection_support_mapsTo X Y B Z πX πY hprod).comp hj) (hy.comp hg) (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have h₃ := SchemeCycle.NormalRestriction.BundleCycles.schemeSupportedCycleClass_regularPairPullback Y B p hp g JZ hg
  exact h₁.trans (h₂.trans (h₃.trans (schemeRegularSupportThomClass_projection X Y B Z πX πY hprod p hp)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularTo.BundleCycles
