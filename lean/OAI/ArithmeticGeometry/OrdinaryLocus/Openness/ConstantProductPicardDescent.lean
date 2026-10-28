import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductToTriple
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPicardDescent

/-! # Constant Product Picard Descent -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPicardDescent.Construction

noncomputable section

/-! Picard descent from two proper modifications to the group triple product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry CartesianMonoidalCategory MonoidalCategory

variable {K : Type} [Field K]

theorem isProper_tensor_hom
    {A B C D : Over (Spec (.of K))} (f : A ⟶ B) (g : C ⟶ D)
    [IsProper f.left] [IsProper g.left] : IsProper (f ⊗ₘ g).left := by
  have : IsProper (f ⊗ₘ 𝟙 C).left :=
    MorphismProperty.of_isPullback (TensorPicardDescent.Construction.isPullback_tensor_left f C) inferInstance
  have : IsProper (𝟙 B ⊗ₘ g).left :=
    MorphismProperty.of_isPullback (TensorPicardDescent.Construction.isPullback_tensor_right g B) inferInstance
  have hc : IsProper ((f ⊗ₘ 𝟙 C).left ≫ (𝟙 B ⊗ₘ g).left) := inferInstance
  exact (congrArg (fun h => IsProper h.left) (tensor_id_comp_id_tensor g f)) ▸ hc

theorem picardPullback_constantProductToTriple_injective
    (A B G : Over (Spec (.of K))) (a : A ⟶ G) (b : B ⟶ G)
    [IsProper a.left] [IsProper b.left]
    (ha : ∀ U : G.left.Opens, IsIso (a.left.app U))
    (hb : ∀ U : G.left.Opens, IsIso (b.left.app U)) :
    Function.Injective (PicardPullback.Construction.picardPullback (ConstantProductToTriple.Construction.constantProductToTriple A B G a b).left) := by
  have : IsProper (a ⊗ₘ b).left := isProper_tensor_hom a b
  have hi := TensorPicardDescent.Construction.picardPullback_tensor_left_injective (a ⊗ₘ b)
    (TensorPicardDescent.Construction.tensor_product_preserves_functions a b ha hb) G
  let e : (ConstantProductCoordinates.Construction.constantProduct A B G).left ≅ ((A ⊗ B) ⊗ G).left :=
    (Over.forget (Spec (.of K))).mapIso (ConstantProductAssociativity.Construction.constantProductAssocIso A B G)
  have he : Function.Injective (PicardPullback.Construction.picardPullback e.hom) := (PicardPullback.Construction.picardPullbackIso e).injective
  change Function.Injective (PicardPullback.Construction.picardPullback (e.hom ≫ ((a ⊗ₘ b) ⊗ₘ 𝟙 G).left))
  rw [PicardPullback.Construction.picardPullback_comp]
  exact he.comp hi

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ConstantProductPicardDescent.Construction
