import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Mono Sheaf Local Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MonoSheafLocalImage.Construction

noncomputable section

/-! A section locally in the image of an injective map of sheaves
has a unique global preimage. This is actual sheaf gluing. -/

open _root_.CategoryTheory Opposite

universe u v w

theorem existsUnique_preimage_of_covering_imageSieve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type w)} (f : F ⟶ G) [Mono f.hom]
    (T : C) (s : G.obj.obj (op T)) (hs : Presheaf.imageSieve f.hom s ∈ J T) :
    ∃! t : F.obj.obj (op T), f.hom.app (op T) t = s := by
  have hi (X : Cᵒᵖ) : Function.Injective (f.hom.app X) :=
    (CategoryTheory.mono_iff_injective _).mp inferInstance
  have H := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property _ hs
  let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
    fun _ g hg => Presheaf.localPreimage f.hom s g hg
  have ht : t.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
    apply hi
    have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
    have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
    have eq₃ := congrArg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
    have eq₄ := congrArg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
    refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    simp only [← op_comp, hcomp]
  have hv : f.hom.app (op T) (H.amalgamate t ht) = s := by
    apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _ hs).ext
    intro Y g hg
    rw [← NatTrans.naturality_apply, H.valid_glue ht]
    exact Presheaf.app_localPreimage f.hom s g hg
  exact ⟨H.amalgamate t ht, hv, fun t' ht' => hi _ (ht'.trans hv.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MonoSheafLocalImage.Construction
