import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Homogeneous Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPullback

noncomputable section

/-! Pullback by a group-scheme morphism preserves homogeneous Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g h : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
  (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem translation_pullback_naturality {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ (T ◁ f) = (T ◁ f) ≫ B.translation (a ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation, MonObj.mul_comp, MonObj.comp_mul, Category.assoc]

theorem relativePicardPullbackPresheaf_translation {T : Over S}
    (a : T ⟶ A.scheme) (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (.op T)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
        ((SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) q) =
      (SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left q) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q)
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, translation_pullback_naturality]

theorem homogeneousPicardClass_pullback {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (.op T)}
    (hq : B.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T ((SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) q) := by
  intro U t a
  have heq := hq U t (a ≫ f)
  have hm := congrArg ((SheafMaps.Construction.relativePicardPullback f).hom.app (.op U)) heq
  rw [SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply,
    SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at hm
  have hn := (SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply t.op q
  rw [← hn]
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U))
    (relativePicardPullbackPresheaf_translation A B f a
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map t.op q))).trans hm

def homogeneousPicardPullbackPresheaf :
    B.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := TypeCat.ofHom fun q =>
    ⟨(SheafMaps.Construction.relativePicardPullbackPresheaf f).app T q.val,
      homogeneousPicardClass_pullback A B f q.property⟩
  naturality {T U} t := by
    ext q
    apply Subtype.ext
    exact (SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply t q.val

def homogeneousPicardPullback : B.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardPullbackPresheaf A B f)

theorem homogeneousPicardPullback_inclusion :
    homogeneousPicardPullback A B f ≫ A.homogeneousPicardSheafInclusion =
      B.homogeneousPicardSheafInclusion ≫ SheafMaps.Construction.relativePicardPullback f := by
  have h : homogeneousPicardPullbackPresheaf A B f ≫ A.homogeneousPicardInclusion =
      B.homogeneousPicardInclusion ≫ SheafMaps.Construction.relativePicardPullbackPresheaf f := rfl
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

theorem homogeneousPicardPullback_trivial (T : Over S) :
    (homogeneousPicardPullback A B f).hom.app (.op T)
        (B.trivialHomogeneousPicardClass T) = A.trivialHomogeneousPicardClass T := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (homogeneousPicardPullbackPresheaf A B f)) (.op T))
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, B.trivialClass_homogeneous T⟩
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T))
    (Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T ◁ f).left)))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousPullback
