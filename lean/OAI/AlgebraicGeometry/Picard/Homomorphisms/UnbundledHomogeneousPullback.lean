import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneous
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps

/-! # Unbundled Homogeneous Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback

noncomputable section

/-! Dimension-independent homogeneous pullback,
using the actual line bundles and represented homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} (A B : Over S) [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]

theorem translation_pullback_naturality {T : Over S} (a : T ⟶ A) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a ≫ (T ◁ f) = (T ◁ f) ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.translation B) (a ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [UnbundledHomogeneous.Construction.UnbundledPicard.translation, MonObj.mul_comp, MonObj.comp_mul, Category.assoc]

theorem relativePicardPullbackPresheaf_translation {T : Over S}
    (a : T ⟶ A) (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op T)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left
        ((SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) q) =
      (SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation B) (a ≫ f)).left q) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left q) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation B) (a ≫ f)).left q)
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, translation_pullback_naturality]

theorem homogeneousPicardClass_pullback {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op T)}
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B) T q) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) T ((SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) q) := by
  intro U t a
  have heq := hq U t (a ≫ f)
  have hm := congrArg ((SheafMaps.Construction.relativePicardPullback f).hom.app (.op U)) heq
  rw [SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply,
    SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at hm
  have hn := (SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply t.op q
  rw [← hn]
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U))
    (relativePicardPullbackPresheaf_translation A B f a
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map t.op q))).trans hm

def homogeneousPicardPullbackPresheaf :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B) ⟶ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A) where
  app T := TypeCat.ofHom fun q =>
    ⟨(SheafMaps.Construction.relativePicardPullbackPresheaf f).app T q.val,
      homogeneousPicardClass_pullback A B f q.property⟩
  naturality {T U} t := by
    ext q
    apply Subtype.ext
    exact (SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply t q.val

def homogeneousPicardPullback : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B) ⟶ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardPullbackPresheaf A B f)

theorem homogeneousPicardPullback_inclusion :
    homogeneousPicardPullback A B f ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B) ≫ SheafMaps.Construction.relativePicardPullback f := by
  have h : homogeneousPicardPullbackPresheaf A B f ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion B) ≫ SheafMaps.Construction.relativePicardPullbackPresheaf f := rfl
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))

theorem homogeneousPicardPullback_trivial (T : Over S) :
    (homogeneousPicardPullback A B f).hom.app (.op T)
        ((UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B) T) = (UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A) T := by
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (homogeneousPicardPullbackPresheaf A B f)) (.op T))
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, (UnbundledHomogeneous.Construction.UnbundledPicard.trivialClass_homogeneous B) T⟩
  exact hn.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (.op T))
    (Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T ◁ f).left)))

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousPullback
