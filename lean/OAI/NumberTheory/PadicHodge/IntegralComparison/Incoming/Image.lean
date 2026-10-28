import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatFromNonemptyLimits
import OAI.NumberTheory.PadicHodge.IntegralComparison.InitialConstantMaps

/-! # Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Image

noncomputable section

/-!
# IntegralComparison: factor a functor through objects mapping to its image

On this full subcategory, the incoming categories are nonempty. Preserved
binary products and equalizers make the factor functor final. If the full
subcategory covers the target site, sheaf descent then gives the actual
constant-source presheaf Hom comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D)

def property : ObjectProperty D := fun T => Nonempty (StructuredArrow T F)

abbrev Objects := (Image.property F).FullSubcategory
abbrev inclusion : Objects F ⥤ D := (Image.property F).ι

abbrev factor : C ⥤ Objects F :=
  (Image.property F).lift F (fun X => ⟨StructuredArrow.mk (𝟙 (F.obj X))⟩)

lemma incoming_nonempty (T : Objects F) : Nonempty (StructuredArrow T (factor F)) := by
  obtain ⟨a⟩ := T.property
  exact ⟨StructuredArrow.mk (Y := a.right) (ObjectProperty.homMk a.hom)⟩

variable [HasBinaryProducts C] [HasEqualizers C]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F] [PreservesLimitsOfShape WalkingParallelPair F]

instance factor_preservesProducts : PreservesLimitsOfShape (Discrete WalkingPair) (factor F) := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) (factor F ⋙ inclusion F) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete WalkingPair) F)
  exact preservesLimitsOfShape_of_reflects_of_preserves (factor F) (inclusion F)

instance factor_preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair (factor F) := by
  have : PreservesLimitsOfShape WalkingParallelPair (factor F ⋙ inclusion F) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingParallelPair F)
  exact preservesLimitsOfShape_of_reflects_of_preserves (factor F) (inclusion F)

instance factor_flat : RepresentablyFlat (factor F) :=
  FlatFromNonemptyLimits.flat (factor F) (incoming_nonempty F)

instance factor_final : (factor F).Final := final_of_representablyFlat _

variable (K : GrothendieckTopology D) [(inclusion F).IsCoverDense K]
variable (E : Type u'') [Category.{v''} E] (M : E) (Y : Sheaf K E)

lemma constant_restriction_bijective : Function.Bijective
    (Functor.whiskerLeft F.op : ((Functor.const Dᵒᵖ).obj M ⟶ Y.obj) →
      ((Functor.const Cᵒᵖ).obj M ⟶ F.op ⋙ Y.obj)) := by
  have h₁ := (Functor.IsCoverDense.restrictHomEquivHom
    (G := inclusion F) (ℱ := (Functor.const Dᵒᵖ).obj M) (ℱ' := Y)).symm.bijective
  have h₂ := InitialConstantMaps.bijective (factor F).op M ((inclusion F).op ⋙ Y.obj)
  exact h₂.comp h₁

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Image
