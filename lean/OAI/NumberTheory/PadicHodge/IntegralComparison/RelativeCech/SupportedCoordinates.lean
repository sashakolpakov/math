import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechForget

/-! # Supported Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates

noncomputable section

/-! Coordinates of the original global-to-supported lift in the relative
Čech construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.GlobalSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  (X : TopCat.{u}) (U : Opens X) {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  (O : Opens X) (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
  (hzero : ∀ q, IsZero ((K.X q).obj.obj (op O)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Intersections.intersect U
abbrev terminalOpen : Opens X := (Intersections.intersect U).obj (⊤_ (Opens X))
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates.terminalOpen X U

def underlying : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) D).mapHomologicalComplex (.up ℕ)).obj K

theorem local_component (q : ℕ) :
    (Supported.ZeroComplementComplex.lift O A K hzero).f q ≫
      SupportedOrderedCechEdge.Abelian.component D X F V O K q =
        GlobalSections.relativeAugmentation U V (K.X q).obj := by
  have hlift : (Supported.ZeroComplementComplex.lift O A K hzero).f q ≫
      (Supported.SectionsExcision.inclusion A (A ⊓ O) inf_le_left).app (K.X q) =
        (K.X q).obj.map (homOfLE (le_top : A ≤ ⊤)).op :=
    congrArg (fun f => f.f q)
      (Supported.ZeroComplementComplex.lift_inclusion O A K hzero)
  apply Pi.hom_ext
  intro (a : AugmentedOrdered.Cech.Index ι 0)
  change ((Supported.ZeroComplementComplex.lift O A K hzero).f q ≫
      ((Supported.SectionsExcision.inclusion A (A ⊓ O) inf_le_left).app (K.X q) ≫
        (AugmentedOrdered.CechZero.zeroIso V ((F).op ⋙ (K.X q).obj)).inv)) ≫
      ExtensionComponents.sourceProjection U V (K.X q).obj a =
    GlobalSections.relativeAugmentation U V (K.X q).obj ≫
      ExtensionComponents.sourceProjection U V (K.X q).obj a
  rw [GlobalSections.relativeAugmentation_projection]
  suffices ((Supported.ZeroComplementComplex.lift O A K hzero).f q ≫
      (Supported.SectionsExcision.inclusion A (A ⊓ O) inf_le_left).app (K.X q)) ≫
      ((AugmentedOrdered.CechZero.zeroIso V ((F).op ⋙ (K.X q).obj)).inv ≫
        ExtensionComponents.sourceProjection U V (K.X q).obj a) =
      (K.X q).obj.map (homOfLE (le_top :
        U ⊓ (AugmentedOrdered.Cech.formal V 0).obj a ≤ ⊤)).op by
    simpa only [Category.assoc] using this
  rw [hlift]
  erw [AugmentedOrdered.CechZero.zeroIso_inv_π]
  change (K.X q).obj.map _ ≫ (K.X q).obj.map _ = (K.X q).obj.map _
  rw [← Functor.map_comp]
  congr 1

variable (hV : ∀ i, V i ≤ O)

include hzero hV in
omit [HasLimitsOfSize.{u, u, u, u + 1} D] [LinearOrder ι] in
theorem restriction_zero (q : ℕ) (i : ι) :
    (K.X q).obj.map (homOfLE (le_top : V i ≤ ⊤)).op = 0 := by
  have h : (homOfLE (le_top : V i ≤ ⊤)) =
      (homOfLE (hV i)) ≫ homOfLE (le_top : O ≤ ⊤) := Subsingleton.elim _ _
  have hz : (K.X q).obj.map (homOfLE (le_top : O ≤ ⊤)).op = 0 :=
    (hzero q).eq_zero_of_tgt _
  rw [h, op_comp, Functor.map_comp, hz, zero_comp]

include hV in
theorem global_component (q : ℕ) :
    ((Supported.ZeroComplementComplex.lift O A K hzero).f q ≫
      SupportedOrderedCechEdge.Abelian.component D X F V O K q) ≫
        ExtensionComponents.component U V (K.X q).obj 0 =
      GlobalSections.globalAugmentation (Intersections.cover U V) (K.X q).obj := by
  rw [local_component D X U V O K hzero q]
  simpa only [Category.id_comp] using
    GlobalSections.augmentation U V (K.X q).obj (𝟙 _) (fun i => by
      simpa only [Category.id_comp] using restriction_zero D X V O K hzero hV q i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedCoordinates
