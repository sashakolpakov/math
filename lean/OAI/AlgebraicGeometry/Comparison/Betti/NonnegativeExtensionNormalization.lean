import OAI.AlgebraicGeometry.Comparison.Betti.AugmentationExtension

/-! # Nonnegative Extension Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNormalization.Complex

noncomputable section

/-! The two existing embeddings of nonnegative cochains into integer
cochains agree canonically, including the actual injective augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.Complex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {e e' : c.Embedding c'}

def extensionIsoOfEq (h : e = e') (K : HomologicalComplex C c) : K.extend e ≅ K.extend e' :=
  eqToIso (congrArg (fun k => K.extend k) h)

theorem extensionIsoOfEq_hom_f (h : e = e') (K : HomologicalComplex C c)
    {i : ι} {j : ι'} (hi : e.f i = j) (hi' : e'.f i = j) :
    (extensionIsoOfEq h K).hom.f j ≫ (K.extendXIso e' hi').hom = (K.extendXIso e hi).hom := by
  subst e'
  simp [extensionIsoOfEq]

theorem embeddingUpIntGE_zero_eq : ComplexShape.embeddingUpIntGE 0 = ComplexShape.embeddingUpNat := by
  have h : (ComplexShape.embeddingUpIntGE 0).f = ComplexShape.embeddingUpNat.f := by
    funext n
    simp
  have heq (a b : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))
      (hab : a.f = b.f) : a = b := by
    cases a
    cases b
    cases hab
    rfl
  exact heq _ _ h

def nonnegativeExtensionIso (K : CochainComplex C ℕ) :
    K.extend (ComplexShape.embeddingUpIntGE 0) ≅ K.extend ComplexShape.embeddingUpNat :=
  extensionIsoOfEq embeddingUpIntGE_zero_eq K

theorem nonnegativeExtensionIso_cocycle (K : CochainComplex C ℕ) (n : ℕ) :
    (K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := n) (i' := (n : ℤ)) (by simp)).inv ≫
        (nonnegativeExtensionIso K).hom.f (n : ℤ) =
      (K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).inv := by
  apply (cancel_mono (K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).hom).mp
  erw [Category.assoc, extensionIsoOfEq_hom_f embeddingUpIntGE_zero_eq K (by simp) rfl,
    Iso.inv_hom_id, Iso.inv_hom_id]

theorem nonnegativeExtensionIso_injective_augmentation {Z : C} (I : InjectiveResolution Z) :
    AugmentationExtension.Complex.extendAugmentation I.ι ≫ (nonnegativeExtensionIso I.cocomplex).hom = I.ι' := by
  apply HomologicalComplex.from_single_hom_ext
  change (AugmentationExtension.Complex.extendAugmentation I.ι).f 0 ≫ (nonnegativeExtensionIso I.cocomplex).hom.f 0 = I.ι'.f 0
  erw [AugmentationExtension.Complex.extendAugmentation_f_zero, I.ι'_f_zero]
  change (_ ≫ AugmentationExtension.Complex.augmentationZero I.ι ≫ _) ≫ _ = _
  erw [Category.assoc, Category.assoc, nonnegativeExtensionIso_cocycle I.cocomplex 0]
  simp only [AugmentationExtension.Complex.augmentationZero, CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  erw [Category.id_comp (I.ι.f 0)]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.NonnegativeExtensionNormalization.Complex
