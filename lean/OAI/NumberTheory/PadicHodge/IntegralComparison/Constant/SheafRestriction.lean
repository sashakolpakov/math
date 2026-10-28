import OAI.NumberTheory.PadicHodge.IntegralComparison.InitialConstantMaps

/-! # Sheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction

noncomputable section

/-!
# IntegralComparison: constant-source Hom comparison on sheaves

For a continuous and cocontinuous functor whose opposite is initial,
restriction is bijective on morphisms from a constant sheaf. Compatibility
with sheafification identifies this bijection with the actual restriction
map, rather than with an unrelated abstract equivalence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (E : Type u'') [Category.{v''} E]
variable [F.IsContinuous J K] [F.IsCocontinuous J K] [F.op.Initial]
variable [HasWeakSheafify J E] [HasWeakSheafify K E]
variable [∀ P : Cᵒᵖ ⥤ E, F.op.HasPointwiseRightKanExtension P]
variable (M : E)

abbrev restriction := F.sheafPushforwardContinuous E J K

abbrev constant := (constantSheaf K E).obj M

def compatibility : (presheafToSheaf J E).obj (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ≅ (restriction F J K E).obj (constant K E M) :=
  (F.pushforwardContinuousSheafificationCompatibility E J K).app ((Functor.const Dᵒᵖ).obj M)

def targetEquiv (Y : Sheaf K E) :
    ((restriction F J K E).obj (constant K E M) ⟶ (restriction F J K E).obj Y) ≃
      ((Functor.const Cᵒᵖ).obj M ⟶ F.op ⋙ Y.obj) :=
  (Iso.homCongr (compatibility F J K E M).symm (Iso.refl _)).trans
    ((sheafificationAdjunction J E).homEquiv _ _)

omit [F.op.Initial] in
lemma targetEquiv_apply (Y : Sheaf K E)
    (g : (restriction F J K E).obj (constant K E M) ⟶ (restriction F J K E).obj Y) :
    targetEquiv F J K E M Y g =
      toSheafify J (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ≫ (compatibility F J K E M).hom.hom ≫ g.hom := by
  change (sheafificationAdjunction J E).homEquiv _ _ ((compatibility F J K E M).hom ≫ g ≫ 𝟙 _) = _
  rw [Category.comp_id, Adjunction.homEquiv_unit]
  rfl

omit [F.op.Initial] in
lemma compatibility_unit : toSheafify J (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ≫
    (compatibility F J K E M).hom.hom =
      Functor.whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)) :=
  F.toSheafify_pullbackSheafificationCompatibility E J K ((Functor.const Dᵒᵖ).obj M)

omit [F.op.Initial] in
lemma targetEquiv_map (Y : Sheaf K E) (g : constant K E M ⟶ Y) :
    targetEquiv F J K E M Y ((restriction F J K E).map g) =
      InitialConstantMaps.restrict F.op M Y.obj
        ((sheafificationAdjunction K E).homEquiv _ _ g) := by
  rw [targetEquiv_apply]
  have hg : (sheafificationAdjunction K E).homEquiv _ _ g =
      toSheafify K ((Functor.const Dᵒᵖ).obj M) ≫ g.hom :=
    Adjunction.homEquiv_unit (sheafificationAdjunction K E) _ _ g
  rw [hg]
  let e : sheafify J (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ⟶
      F.op ⋙ sheafify K ((Functor.const Dᵒᵖ).obj M) := (compatibility F J K E M).hom.hom
  let g' : sheafify K ((Functor.const Dᵒᵖ).obj M) ⟶ Y.obj := g.hom
  have hu : toSheafify J (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ≫ e =
      Functor.whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)) := compatibility_unit F J K E M
  change toSheafify J (F.op ⋙ (Functor.const Dᵒᵖ).obj M) ≫ e ≫ Functor.whiskerLeft F.op g' =
    Functor.whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj M) ≫ g')
  rw [← Category.assoc, hu, Functor.whiskerLeft_comp]

def homEquivalence (Y : Sheaf K E) :
    (constant K E M ⟶ Y) ≃
      ((restriction F J K E).obj (constant K E M) ⟶ (restriction F J K E).obj Y) :=
  ((sheafificationAdjunction K E).homEquiv _ _).trans
    ((InitialConstantMaps.equivalence F.op M Y.obj).trans
      (targetEquiv F J K E M Y).symm)

lemma homEquivalence_apply (Y : Sheaf K E) (g : constant K E M ⟶ Y) :
    homEquivalence F J K E M Y g = (restriction F J K E).map g := by
  apply (targetEquiv F J K E M Y).injective
  exact ((targetEquiv F J K E M Y).apply_symm_apply _).trans (targetEquiv_map F J K E M Y g).symm

lemma map_bijective (Y : Sheaf K E) : Function.Bijective
    ((restriction F J K E).map : (constant K E M ⟶ Y) →
      ((restriction F J K E).obj (constant K E M) ⟶ (restriction F J K E).obj Y)) := by
  have he : (homEquivalence F J K E M Y : _ → _) = (restriction F J K E).map :=
    funext (homEquivalence_apply F J K E M Y)
  exact he ▸ (homEquivalence F J K E M Y).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction
