import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Translation Family Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Homomorphisms of abelian schemes intertwine translation and pullback of Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}

/-- Translation commutes with a group-scheme homomorphism. -/
theorem Abelian.Schemes.AbelianScheme.translation_familyMap (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ (𝟙 T ⊗ₘ f) = (𝟙 T ⊗ₘ f) ≫ B.translation (a ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc, MonObj.comp_mul]
    rw [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_snd, MonObj.mul_comp, Category.assoc]

/-- Pulling back a translated bundle class is the translate of its pullback. -/
theorem Abelian.Schemes.AbelianScheme.translationClass_familyMap (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (a : T ⟶ A.scheme) (q : Line.Bundles.LineBundle.IsoClass (T ⊗ B.scheme).left) :
    Line.Bundles.LineBundle.pullbackClass (𝟙 T ⊗ₘ f).left
      (Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q) =
    Line.Bundles.LineBundle.pullbackClass (A.translation a).left (Line.Bundles.LineBundle.pullbackClass (𝟙 T ⊗ₘ f).left q) := by
  have he : (𝟙 T ⊗ₘ f).left ≫ (B.translation (a ≫ f)).left =
      (A.translation a).left ≫ (𝟙 T ⊗ₘ f).left :=
    (congrArg Over.Hom.left (Abelian.Schemes.AbelianScheme.translation_familyMap f a)).symm
  exact (Line.Bundles.LineBundle.pullbackClass_comp _ _ q).symm.trans
    ((congrArg (fun p => Line.Bundles.LineBundle.pullbackClass p q) he).trans
      (Line.Bundles.LineBundle.pullbackClass_comp _ _ q))

/-- Translation invariance in the Picard sheaf is preserved by pullback along group homomorphisms. -/
theorem Abelian.Schemes.AbelianScheme.TranslationInvariant.familyMap (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (a : T ⟶ A.scheme) (q : Line.Bundles.LineBundle.IsoClass (T ⊗ B.scheme).left)
    (hq : B.TranslationInvariant (a ≫ f) q) :
    A.TranslationInvariant a (Line.Bundles.LineBundle.pullbackClass (𝟙 T ⊗ₘ f).left q) := by
  have hm := congrArg (fun z => (Picard.FamilySheafMaps.relativePicardSheafMap f).hom.app (.op T) z) hq
  have hleft := Picard.FamilySheafMaps.relativePicardSheafMap_toRelative f T
    (Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q)
  have hright := Picard.FamilySheafMaps.relativePicardSheafMap_toRelative f T q
  have hc := congrArg (fun z => (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) z)
    (Abelian.Schemes.AbelianScheme.translationClass_familyMap f a q)
  exact hc.symm.trans (hleft.symm.trans (hm.trans hright))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
