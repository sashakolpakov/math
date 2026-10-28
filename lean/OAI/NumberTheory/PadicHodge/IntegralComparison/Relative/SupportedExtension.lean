import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech

/-! # Supported Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedExtension

noncomputable section

/-! The genuine relative Čech extension agrees with extending supported
sections to the whole space. This identifies the two support-forgetting
maps without choosing representatives or normalizing a residue scalar. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  (U : Opens X) {ι : Type v} [LinearOrder ι] (V : ι → Opens X)
  (O : Opens X)

local instance coefficient_limits [UnivLE.{v,z}] : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{v,v,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R
local instance coefficient_products [UnivLE.{v,z}] : HasProducts.{v} (ModuleCat.{z} R) :=
  fun J => by
    let : HasLimitsOfSize.{v,v} (ModuleCat.{z} R) :=
      ModuleCat.hasLimitsOfSize.{v,v,z,u}
    exact HasLimitsOfSize.has_limits_of_shape (Discrete J)
local instance coefficient_coproducts : HasCoproducts.{0} (ModuleCat.{z} R) :=
  fun J => by
    let : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
      ModuleCat.hasColimitsOfSize.{z,u,0,0} R
    exact HasColimitsOfSize.has_colimits_of_shape (Discrete J)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v z} R)) ℕ)
  (hglobal : (RelativeCech.Intersections.intersect U).obj (⊤_ (Opens X)) ⊔ O = ⊤)

private abbrev ambient : Opens X := (RelativeCech.Intersections.intersect U).obj (⊤_ (Opens X))
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedExtension.ambient X U

def underlying : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{max u v z} R) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v z} R)).mapHomologicalComplex (.up ℕ)).obj K

theorem local_component (q : ℕ) :
    Supported.OrderedCechEdge.component.{u,v,v,z} R X (RelativeCech.Intersections.intersect U) V O K q =
      (Supported.SectionsExcision.extensionComplex O A hglobal K).f q ≫
        RelativeCech.GlobalSections.relativeAugmentation U V (K.X q).obj := by
  have he := Supported.SectionsExcision.extension_restriction O A hglobal (K.X q)
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 0)
  change ((Supported.SectionsExcision.inclusion A (A ⊓ O) inf_le_left).app (K.X q) ≫
      (AugmentedOrdered.CechZero.zeroIso V ((RelativeCech.Intersections.intersect U).op ⋙ (K.X q).obj)).inv) ≫
        RelativeCech.ExtensionComponents.sourceProjection U V (K.X q).obj a =
    ((Supported.SectionsExcision.extension O A hglobal).app (K.X q) ≫
      RelativeCech.GlobalSections.relativeAugmentation U V (K.X q).obj) ≫
        RelativeCech.ExtensionComponents.sourceProjection U V (K.X q).obj a
  rw [Category.assoc]
  erw [AugmentedOrdered.CechZero.zeroIso_inv_π]
  rw [Category.assoc, RelativeCech.GlobalSections.relativeAugmentation_projection, ← he]
  change (_ ≫ (K.X q).obj.map (homOfLE (le_top : A ≤ ⊤)).op) ≫
      (K.X q).obj.map _ = _
  rw [Category.assoc, ← (K.X q).obj.map_comp]
  congr 2

theorem extension_zero (q : ℕ) :
    (Supported.SectionsExcision.extensionComplex O A hglobal K).f q ≫
      (K.X q).obj.map (homOfLE (le_top : O ≤ ⊤)).op = 0 := by
  change ((Supported.SectionsExcision.excisionIso O A hglobal).inv.app (K.X q) ≫
      kernel.ι ((Supported.SectionsExcision.restriction ⊤ O le_top).app (K.X q))) ≫
        ((Supported.SectionsExcision.restriction ⊤ O le_top).app (K.X q)) = 0
  rw [Category.assoc, kernel.condition, comp_zero]

variable (hV : ∀ i, V i ≤ O)

include hV in
omit [LinearOrder ι] in
theorem complementary_zero (q : ℕ) (i : ι) :
    (Supported.SectionsExcision.extensionComplex O A hglobal K).f q ≫
      (K.X q).obj.map (homOfLE (le_top : V i ≤ ⊤)).op = 0 := by
  have h : (homOfLE (le_top : V i ≤ ⊤)) =
      (homOfLE (hV i)) ≫ homOfLE (le_top : O ≤ ⊤) := Subsingleton.elim _ _
  rw [h, op_comp, Functor.map_comp, ← Category.assoc,
    extension_zero R X U O K hglobal, zero_comp]

include hV in
theorem global_component (q : ℕ) :
    Supported.OrderedCechEdge.component.{u,v,v,z} R X (RelativeCech.Intersections.intersect U) V O K q ≫
      RelativeCech.ExtensionComponents.component U V (K.X q).obj 0 =
    (Supported.SectionsExcision.extensionComplex O A hglobal K).f q ≫
      RelativeCech.GlobalSections.globalAugmentation (RelativeCech.Intersections.cover U V) (K.X q).obj := by
  rw [local_component R X U V O K hglobal q]
  exact RelativeCech.GlobalSections.augmentation U V (K.X q).obj
    ((Supported.SectionsExcision.extensionComplex O A hglobal K).f q)
    (complementary_zero R X U V O K hglobal hV q)

include hV in
def relativeMap :=
    Supported.OrderedCechEdge.map.{u,v,v,z} R X (RelativeCech.Intersections.intersect U) V O K
        (fun i => inf_le_right.trans (hV i)) ≫
      RelativeCech.Total.map U V (underlying.{u,v,z} R X K)

def globalMap :=
    Supported.SectionsExcision.extensionComplex O A hglobal K ≫
      Presheaf.OrderedCechEdge.edge (RelativeCech.Intersections.cover U V) (underlying.{u,v,z} R X K)

include hV in
theorem comparison : relativeMap R X U V O K hV = globalMap R X U V O K hglobal := by
  unfold relativeMap globalMap
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, Supported.OrderedCechEdge.map,
    RelativeCech.Total.map, Presheaf.OrderedCechEdge.edge,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (RelativeCech.Total.target U V (underlying.{u,v,z} R X K)).ιTotal
      (.up ℕ) q 0 q rfl) (global_component R X U V O K hglobal hV q)).trans
        (Category.assoc _ _ _))

variable (hcover : (RelativeCech.Intersections.intersect U).obj (⊤_ (Opens X)) ⊓ O ≤
    ⨆ i, (RelativeCech.Intersections.intersect U).obj (V i))
  (hrows : ∀ q r, ((Supported.OrderedCechEdge.bicomplex.{u,v,v,z}
    R X (RelativeCech.Intersections.intersect U) V K).X q).ExactAt (r+1))

include hV in
theorem homology_comparison (q : ℕ) :
    homologyMap (RelativeCech.Total.map U V (underlying.{u,v,z} R X K)) q =
      Supported.OrderedCech.Comparison.forgetSupport.{u,v,v,z} R X
        (RelativeCech.Intersections.intersect U) V O K (fun i => inf_le_right.trans (hV i)) hcover hrows hglobal q ≫
      homologyMap (Presheaf.OrderedCechEdge.edge (RelativeCech.Intersections.cover U V) (underlying.{u,v,z} R X K)) q := by
  let e := Supported.OrderedCech.Comparison.homologyIso.{u,v,v,z} R X
    (RelativeCech.Intersections.intersect U) V O K (fun i => inf_le_right.trans (hV i)) hcover hrows q
  have h := congrArg (fun a => homologyMap a q)
    (comparison R X U V O K hglobal hV)
  dsimp only [relativeMap, globalMap] at h
  rw [homologyMap_comp, homologyMap_comp] at h
  change e.hom ≫ _ = _ at h
  calc
    _ = e.inv ≫ (e.hom ≫ homologyMap
        (RelativeCech.Total.map U V (underlying.{u,v,z} R X K)) q) := by
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    _ = _ := by
      rw [h]
      rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedExtension
