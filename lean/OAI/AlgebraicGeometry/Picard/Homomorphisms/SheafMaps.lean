import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Sheaf Maps -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps

noncomputable section

/-!
# Homomorphisms: pullback and p-th tensor powers on the relative Picard sheaf

All operations below are induced from pullback or tensor powers of actual
line bundles and then passed through fppf sheafification.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S}

def relativePicardPullbackPresheaf (f : A ⟶ B) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A where
  app T := TypeCat.ofHom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left)
  naturality {T U} h := by
    ext q
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (U.unop ◁ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (h.unop ▷ B).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (h.unop ▷ A).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left q)
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
      ← Over.comp_left, ← Over.comp_left, whisker_exchange]

def relativePicardPullback (f : A ⟶ B) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (relativePicardPullbackPresheaf f)

theorem relativePicardPullback_toRelativePicard (f : A ⟶ B) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B ≫ (relativePicardPullback f).hom =
      relativePicardPullbackPresheaf f ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A :=
  (toSheafify_naturality _ _).symm

theorem relativePicardPullback_toRelativePicard_apply (f : A ⟶ B) (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op T)) :
    (relativePicardPullback f).hom.app (.op T) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op T) q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) ((relativePicardPullbackPresheaf f).app (.op T) q) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (relativePicardPullback_toRelativePicard f) (.op T)) q

variable (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0)

def relativePicardTensorPowerPresheaf (A : Over S) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A where
  app _ := TypeCat.ofHom (LineBundleClasses.Construction.tensorPowerClass p)
  naturality {T U} h := by
    ext q
    exact (LineBundleClasses.Construction.tensorPowerClass_pullback p hp
      (Frobenius.Construction.prime_eq_zero_of_map p hS (U.unop ⊗ A).hom)
      (Frobenius.Construction.prime_eq_zero_of_map p hS (T.unop ⊗ A).hom) (h.unop ▷ A).left q).symm

def relativePicardTensorPower (A : Over S) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (relativePicardTensorPowerPresheaf p hp hS A)

theorem relativePicardTensorPower_toRelativePicard (A : Over S) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A ≫ (relativePicardTensorPower p hp hS A).hom =
      relativePicardTensorPowerPresheaf p hp hS A ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A :=
  (toSheafify_naturality _ _).symm

theorem relativePicardTensorPower_toRelativePicard_apply (A : Over S) (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (.op T)) :
    (relativePicardTensorPower p hp hS A).hom.app (.op T)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) q) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (LineBundleClasses.Construction.tensorPowerClass p q) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (relativePicardTensorPower_toRelativePicard p hp hS A) (.op T)) q

theorem relativePicardTensorPowerPresheaf_pullback (f : A ⟶ B) :
    relativePicardTensorPowerPresheaf p hp hS B ≫ relativePicardPullbackPresheaf f =
      relativePicardPullbackPresheaf f ≫ relativePicardTensorPowerPresheaf p hp hS A := by
  ext T q
  exact LineBundleClasses.Construction.tensorPowerClass_pullback p hp
    (Frobenius.Construction.prime_eq_zero_of_map p hS (T.unop ⊗ A).hom)
    (Frobenius.Construction.prime_eq_zero_of_map p hS (T.unop ⊗ B).hom) (T.unop ◁ f).left q

theorem relativePicardTensorPower_pullback (f : A ⟶ B) :
    relativePicardTensorPower p hp hS B ≫ relativePicardPullback f =
      relativePicardPullback f ≫ relativePicardTensorPower p hp hS A := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (relativePicardTensorPowerPresheaf_pullback p hp hS f)).trans
      (F.map_comp _ _))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps
