import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Image

/-! # Local Constant Sheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalConstantSheafRestriction

noncomputable section

/-!
# IntegralComparison: constant-source sheaf comparison from local incoming presentations

A covering incoming-image subcategory gives constant-source presheaf
comparison. Compatibility with sheafification identifies this with the
actual restriction map on sheaf morphisms.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' u'' v''

open OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (E : Type u'') [Category.{v''} E]
variable [F.IsContinuous J K] [F.IsCocontinuous J K]
variable [HasWeakSheafify J E] [HasWeakSheafify K E]
variable [∀ P : Cᵒᵖ ⥤ E, F.op.HasPointwiseRightKanExtension P]
variable (M : E) (Y : Sheaf K E)

lemma map_bijective_of_presheaf
    (h : Function.Bijective (InitialConstantMaps.restrict F.op M Y.obj)) :
    Function.Bijective ((Constant.SheafRestriction.restriction F J K E).map : (Constant.SheafRestriction.constant K E M ⟶ Y) →
      ((Constant.SheafRestriction.restriction F J K E).obj (Constant.SheafRestriction.constant K E M) ⟶ (Constant.SheafRestriction.restriction F J K E).obj Y)) := by
  let e := ((sheafificationAdjunction K E).homEquiv ((Functor.const Dᵒᵖ).obj M) Y).trans
    ((Equiv.ofBijective (InitialConstantMaps.restrict F.op M Y.obj) h).trans
      (Constant.SheafRestriction.targetEquiv F J K E M Y).symm)
  have he : (e : _ → _) = (Constant.SheafRestriction.restriction F J K E).map := by
    funext g
    apply (Constant.SheafRestriction.targetEquiv F J K E M Y).injective
    exact ((Constant.SheafRestriction.targetEquiv F J K E M Y).apply_symm_apply _).trans (Constant.SheafRestriction.targetEquiv_map F J K E M Y g).symm
  exact he ▸ e.bijective

variable [HasBinaryProducts C] [HasEqualizers C]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F] [PreservesLimitsOfShape WalkingParallelPair F]
variable [(Incoming.Image.inclusion F).IsCoverDense K]

lemma map_bijective : Function.Bijective ((Constant.SheafRestriction.restriction F J K E).map : (Constant.SheafRestriction.constant K E M ⟶ Y) →
    ((Constant.SheafRestriction.restriction F J K E).obj (Constant.SheafRestriction.constant K E M) ⟶ (Constant.SheafRestriction.restriction F J K E).obj Y)) :=
  map_bijective_of_presheaf F J K E M Y
    (Incoming.Image.constant_restriction_bijective F K E M Y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalConstantSheafRestriction
