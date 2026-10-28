import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology

/-! # Good Smooth Map -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions

/-! The constructed generic normalization cover embeds into the actual smooth normalization retained for the divisor computation, and both have the same original ambient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem goodOpen_subset_smoothBase (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom] :
    GenericCover.Constructions.goodOpen X ≤ SmoothLocus.Constructions.Open.normalizationSmoothBase X.left X.hom := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X.left) := Normalization.Scheme.Constructions.normalizationMap_isFinite X.left X.hom
  let : LocallyOfFiniteType (GenericCover.Constructions.normalizationOver X).hom := by
    change LocallyOfFiniteType (Normalization.Scheme.Constructions.normalizationMap X.left ≫ X.hom)
    infer_instance
  let : Smooth (((GenericCover.Constructions.normalizationOverMap X).left ⁻¹ᵁ GenericCover.Constructions.goodOpen X).ι ≫ (GenericCover.Constructions.normalizationOver X).hom) :=
    (GenericCover.Constructions.goodOpen_spec X).2.2.2.2
  have hs := ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus (GenericCover.Constructions.normalizationOver X).hom ((GenericCover.Constructions.normalizationOverMap X).left ⁻¹ᵁ GenericCover.Constructions.goodOpen X)
  intro x hx
  rintro ⟨y, hy, hyx⟩
  have hyy : y ∈ (GenericCover.Constructions.normalizationOverMap X).left ⁻¹ᵁ GenericCover.Constructions.goodOpen X := by
    change Normalization.Scheme.Constructions.normalizationMap X.left y ∈ GenericCover.Constructions.goodOpen X
    exact hyx.symm ▸ hx
  exact hy (hs hyy)

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)

theorem goodSource_le_smooth : ((GenericCover.Constructions.normalizationOverMap D.toOver).left ⁻¹ᵁ GenericCover.Constructions.goodOpen D.toOver) ≤
    (AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V D.val := by
  rw [AmbientMap.Constructions.preimage_ambientOpen]
  exact fun _ hx => goodOpen_subset_smoothBase D.toOver hx

def sourceToSmooth : GenericCover.Constructions.sourceOpen D.toOver ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val :=
  Over.homMk ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D)) (by
    change (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D) ≫
      (((AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V D.val).ι ≫
        (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.structureMap)) =
      ((GenericCover.Constructions.normalizationOverMap D.toOver).left ⁻¹ᵁ GenericCover.Constructions.goodOpen D.toOver).ι ≫
        (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.structureMap)
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.structureMap))
        ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_ι (goodSource_le_smooth D))))

instance sourceToSmooth_open : IsOpenImmersion (sourceToSmooth D).left :=
  inferInstanceAs (IsOpenImmersion ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D)))

theorem sourceToSmooth_ambient : sourceToSmooth D ≫ PrincipalBoundary.Constructions.fullAmbientMap V D.val =
    GenericCover.Constructions.coverMap D.toOver ≫ Open.Constructions.targetToAmbient D := by
  apply Over.OverMorphism.ext
  change (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D) ≫ (PrincipalBoundary.Constructions.fullAmbientMap V D.val).left = _
  rw [PrincipalBoundary.Constructions.fullAmbientMap_left]
  change (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D) ≫
      (((AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V D.val).ι ≫
        (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.inclusion)) =
    (Normalization.Scheme.Constructions.normalizationMap D.scheme ∣_ GenericCover.Constructions.goodOpen D.toOver) ≫ ((GenericCover.Constructions.goodOpen D.toOver).ι ≫ D.inclusion)
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.inclusion))
      ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_ι (goodSource_le_smooth D)))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ D.inclusion)
        (morphismRestrict_ι (Normalization.Scheme.Constructions.normalizationMap D.scheme) (GenericCover.Constructions.goodOpen D.toOver)).symm).trans
        (Category.assoc _ _ _)))

end AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.Range

/-! The genuine generic normalization cover contains every smooth-normalization point over the retained ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)

theorem fullAmbientMap_apply (y : (AmbientMap.Constructions.smoothNormalizationOver V D.val).left) :
    (PrincipalBoundary.Constructions.fullAmbientMap V D.val).left y = D.inclusion (Normalization.Scheme.Constructions.normalizationMap D.scheme y.val) := by
  rw [PrincipalBoundary.Constructions.fullAmbientMap_left]
  rfl

theorem sourceToSmooth_mem_range (y : (AmbientMap.Constructions.smoothNormalizationOver V D.val).left) :
    y ∈ Set.range (sourceToSmooth D).left ↔ Normalization.Scheme.Constructions.normalizationMap D.scheme y.val ∈ GenericCover.Constructions.goodOpen D.toOver := by
  constructor
  · rintro ⟨x, rfl⟩
    have he := (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_apply (goodSource_le_smooth D) x
    change Normalization.Scheme.Constructions.normalizationMap D.scheme
      (((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (goodSource_le_smooth D)) x).val ∈ GenericCover.Constructions.goodOpen D.toOver
    exact (congrArg (Normalization.Scheme.Constructions.normalizationMap D.scheme) he).symm ▸ x.property
  · intro hy
    let x : (GenericCover.Constructions.sourceOpen D.toOver).left := ⟨y.val, hy⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_apply (goodSource_le_smooth D) x

theorem sourceToSmooth_range : Set.range (sourceToSmooth D).left =
    (PrincipalBoundary.Constructions.fullAmbientMap V D.val).left ⁻¹' (Open.Constructions.omittedBoundary D : Set V.carrier)ᶜ := by
  ext y
  rw [sourceToSmooth_mem_range]
  change _ ↔ ¬ (PrincipalBoundary.Constructions.fullAmbientMap V D.val).left y ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D (GenericCover.Constructions.goodOpen D.toOver)
  rw [fullAmbientMap_apply]
  have he := Set.ext_iff.mp (ProperImage.Open.Constructions.Construction.supportOpenBoundary_preimage D (GenericCover.Constructions.goodOpen D.toOver))
    (Normalization.Scheme.Constructions.normalizationMap D.scheme y.val)
  exact ((not_congr he).trans not_not).symm

theorem sourceToSmooth_analytic_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (sourceToSmooth D)) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (Open.Constructions.goodAmbient D : Set V.analyticSpace) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion, sourceToSmooth_range]
  rfl

end AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.Range

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

/-! Restricting the genuine finite normalization to an ambient affine open inside the smooth-normalization base gives the actual affine source used for the polynomial graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : V.carrier.Opens)

local instance : IsIntegral (AmbientMap.Constructions.fullNormalizationOver V D.val).left :=
  inferInstanceAs (IsIntegral (Normalization.Scheme.Constructions.normalization D.scheme))

instance normalizationToAmbient_finite : IsFinite (AmbientMap.Constructions.normalizationToAmbient V D.val).left := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap D.scheme) := Normalization.Scheme.Constructions.normalizationMap_isFinite D.scheme D.structureMap
  change IsFinite (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.inclusion)
  infer_instance

def affineBase : Over Foundations.Scheme.ProjectiveSpace.complexBase := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver V.toOver B
def affineSource : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (AmbientMap.Constructions.fullNormalizationOver V D.val) ((AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)
def affineMap : affineSource D B ⟶ affineBase B := ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (AmbientMap.Constructions.normalizationToAmbient V D.val) B
def baseInclusion : affineBase B ⟶ V.toOver := ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion V.toOver B

instance affineMap_finite : IsFinite (affineMap D B).left :=
  inferInstanceAs (IsFinite ((AmbientMap.Constructions.normalizationToAmbient V D.val).left ∣_ B))
instance baseInclusion_open : IsOpenImmersion (baseInclusion B).left :=
  inferInstanceAs (IsOpenImmersion B.ι)

variable (hB : B ≤ AmbientMap.Constructions.ambientOpen V D.val)

include hB in
theorem affineSource_le_smooth : (AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B ≤
    (AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ AmbientMap.Constructions.ambientOpen V D.val := fun _ hx => hB hx

def sourceToSmooth : affineSource D B ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val :=
  Over.homMk ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (affineSource_le_smooth D B hB)) (by
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.structureMap))
        ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_ι (affineSource_le_smooth D B hB))))

instance sourceToSmooth_open : IsOpenImmersion (sourceToSmooth D B hB).left :=
  inferInstanceAs (IsOpenImmersion ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (affineSource_le_smooth D B hB)))

theorem sourceToSmooth_ambient : sourceToSmooth D B hB ≫ PrincipalBoundary.Constructions.fullAmbientMap V D.val =
    affineMap D B ≫ baseInclusion B := by
  apply Over.OverMorphism.ext
  change (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE (affineSource_le_smooth D B hB) ≫
    (PrincipalBoundary.Constructions.fullAmbientMap V D.val).left = _
  rw [PrincipalBoundary.Constructions.fullAmbientMap_left]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (Normalization.Scheme.Constructions.normalizationMap D.scheme ≫ D.inclusion))
      ((Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_ι (affineSource_le_smooth D B hB)))).trans
        (morphismRestrict_ι (AmbientMap.Constructions.normalizationToAmbient V D.val).left B).symm

include hB in
theorem affineSource_smooth : Smooth (affineSource D B).hom := by
  let : Smooth (AmbientMap.Constructions.smoothNormalizationOver V D.val).hom := AmbientMap.Constructions.smoothNormalization_smooth V D.val
  rw [← (sourceToSmooth D B hB).w]
  infer_instance

omit hB in
instance affineBase_smooth : Smooth (affineBase B).hom :=
  inferInstanceAs (Smooth (B.ι ≫ V.structureMap))

omit hB in
instance affineBase_integral [Nonempty B] : IsIntegral (affineBase B).left :=
  inferInstanceAs (IsIntegral (B : Scheme))

omit hB in
instance affineSource_integral [Nonempty ((AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] :
    IsIntegral (affineSource D B).left :=
  inferInstanceAs (IsIntegral (((AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B) : Scheme))

omit hB in
theorem affineSource_affine (hA : IsAffineOpen B) : IsAffine (affineSource D B).left := by
  let : IsAffine (affineBase B).left := hA
  exact isAffine_of_isAffineHom (affineMap D B).left

end AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

end

end OAI
