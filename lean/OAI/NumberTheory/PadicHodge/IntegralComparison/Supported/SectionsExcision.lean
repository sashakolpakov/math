import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechGlobal
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! # Sections Excision -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision

noncomputable section

/-! Sections supported in a closed set extend uniquely from any
open neighborhood of that set. This gives the actual map from local
supported resolution cochains to global resolution cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {D : Type u} [Category.{v} D] [Abelian D] {X : TopCat.{w}}

def sections (U : Opens X) : Sheaf (Opens.grothendieckTopology X) D ⥤ D where
  obj F := F.obj.obj (op U)
  map f := f.hom.app (op U)
  map_id _ := rfl
  map_comp _ _ := rfl

instance sections_additive (U : Opens X) : (sections (D := D) U).Additive where
  map_add := by intros; rfl

def restriction (U V : Opens X) (h : V ≤ U) : sections (D := D) U ⟶ sections V where
  app F := F.obj.map (homOfLE h).op
  naturality _ _ f := (f.hom.naturality (homOfLE h).op).symm

def supported (U V : Opens X) (h : V ≤ U) : Sheaf (Opens.grothendieckTopology X) D ⥤ D where
  obj F := kernel ((restriction U V h).app F)
  map f := kernel.map _ _ ((sections U).map f) ((sections V).map f)
    ((restriction U V h).naturality f).symm
  map_id F := by
    apply (cancel_mono (kernel.ι ((restriction U V h).app F))).mp
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι ((restriction U V h).app _))).mp
    simp

def inclusion (U V : Opens X) (h : V ≤ U) : supported (D := D) U V h ⟶ sections U where
  app F := kernel.ι ((restriction U V h).app F)
  naturality _ _ _ := kernel.lift_ι _ _ _

instance supported_additive (U V : Opens X) (h : V ≤ U) :
    (supported (D := D) U V h).Additive where
  map_add {F G} {f g} := by
    apply (cancel_mono (kernel.ι ((restriction U V h).app G))).mp
    simp only [supported, kernel.map, Preadditive.add_comp, kernel.lift_ι,
      Functor.map_add, Preadditive.comp_add]

def excision (O U : Opens X) :
    supported (D := D) ⊤ O le_top ⟶ supported U (U ⊓ O) inf_le_left where
  app F := kernel.map _ _ ((restriction ⊤ U le_top).app F)
    ((restriction O (U ⊓ O) inf_le_right).app F) (by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)
  naturality F G f := by
    apply (cancel_mono (kernel.ι ((restriction U (U ⊓ O) inf_le_left).app G))).mp
    simpa only [supported, kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc] using
      congrArg (fun a => kernel.ι ((restriction ⊤ O le_top).app F) ≫ a)
        ((restriction ⊤ U le_top).naturality f)

theorem excision_inclusion (O U : Opens X) (F : Sheaf (Opens.grothendieckTopology X) D) :
    (excision O U).app F ≫ (inclusion U (U ⊓ O) inf_le_left).app F =
      (inclusion ⊤ O le_top).app F ≫ (restriction ⊤ U le_top).app F :=
  kernel.lift_ι _ _ _

theorem excision_isIso (O U : Opens X) (hcover : U ⊔ O = ⊤) (F : Sheaf (Opens.grothendieckTopology X) D) :
    IsIso ((excision O U).app F) := by
  have hs : IsPullback
      (F.obj.map (homOfLE le_sup_left : U ⟶ U ⊔ O).op)
      (F.obj.map (homOfLE le_sup_right : O ⟶ U ⊔ O).op)
      (F.obj.map (homOfLE inf_le_left : U ⊓ O ⟶ U).op)
      (F.obj.map (homOfLE inf_le_right : U ⊓ O ⟶ O).op) :=
    IsPullback.of_isLimit (TopCat.Sheaf.isLimitPullbackCone F U O)
  have ht : IsPullback ((restriction ⊤ U le_top).app F)
      ((restriction ⊤ O le_top).app F)
      ((restriction U (U ⊓ O) inf_le_left).app F)
      ((restriction O (U ⊓ O) inf_le_right).app F) := by
    apply hs.of_iso' (F.obj.mapIso (eqToIso hcover).op) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Functor.mapIso_hom, Iso.op_hom, Iso.refl_hom, Category.comp_id]
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
      rw [← F.obj.map_comp]
      congr 1
    · simp only [Functor.mapIso_hom, Iso.op_hom, Iso.refl_hom, Category.comp_id]
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
      rw [← F.obj.map_comp]
      congr 1
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl
  exact isIso_kernel_map_of_isPullback ht.flip

def excisionIso (O U : Opens X) (hcover : U ⊔ O = ⊤) :
    supported (D := D) ⊤ O le_top ≅ supported U (U ⊓ O) inf_le_left :=
  NatIso.ofComponents (fun F => @asIso _ _ _ _ ((excision O U).app F)
    (excision_isIso O U hcover F)) (fun f => (excision O U).naturality f)

def extension (O U : Opens X) (hcover : U ⊔ O = ⊤) :
    supported (D := D) U (U ⊓ O) inf_le_left ⟶ sections ⊤ :=
  (excisionIso O U hcover).inv ≫ inclusion ⊤ O le_top

theorem extension_restriction (O U : Opens X) (hcover : U ⊔ O = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) D) :
    (extension O U hcover).app F ≫ (restriction ⊤ U le_top).app F =
      (inclusion U (U ⊓ O) inf_le_left).app F := by
  change ((excisionIso O U hcover).inv.app F ≫
    (inclusion ⊤ O le_top).app F) ≫ (restriction ⊤ U le_top).app F = _
  rw [Category.assoc, ← excision_inclusion, ← Category.assoc]
  exact (congrArg (fun a => a ≫ (inclusion U (U ⊓ O) inf_le_left).app F)
    ((excisionIso O U hcover).app F).inv_hom_id).trans (Category.id_comp _)

def extensionComplex (O U : Opens X) (hcover : U ⊔ O = ⊤)
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ) :=
  (NatTrans.mapHomologicalComplex (extension O U hcover) (.up ℕ)).app K

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
