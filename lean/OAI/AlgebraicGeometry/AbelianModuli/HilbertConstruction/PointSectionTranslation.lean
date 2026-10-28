import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationSectionFibers

/-! # Point Section Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Translation evaluated at an arbitrary test-scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (T : Over S)

theorem Abelian.Schemes.AbelianScheme.familyPointSection_fst (a : T ⟶ A.scheme) :
    A.familyPointSection T a ≫ Limits.pullback.fst T.hom A.scheme.hom = 𝟙 T.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 T) a)

theorem Abelian.Schemes.AbelianScheme.familyPointSection_translation (a b : T ⟶ A.scheme) :
    A.familyPointSection T b ≫ (A.translation a).left = A.familyPointSection T (a * b) := by
  have h : lift (𝟙 T) b ≫ A.translation a = lift (𝟙 T) (a * b) := by
    simp [Abelian.Schemes.AbelianScheme.translation, MonObj.comp_mul]
  exact congrArg Over.Hom.left h

def PointSectionTranslation.translatedBundle_pointIso (a b : T ⟶ A.scheme) (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) :
    ((L.pullback (A.translation a).left).pullback (A.familyPointSection T b)).sheaf ≅
      (L.pullback (A.familyPointSection T (a * b))).sheaf :=
  (Scheme.Modules.pullbackComp (A.familyPointSection T b) (A.translation a).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (A.familyPointSection_translation T a b)).app L.sheaf

def PointSectionTranslation.baseBundle_pointIso (a : T ⟶ A.scheme) (B : Line.Bundles.LineBundle T.left) :
    ((B.pullback (Limits.pullback.fst T.hom A.scheme.hom)).pullback (A.familyPointSection T a)).sheaf ≅ B.sheaf :=
  (Scheme.Modules.pullbackComp (A.familyPointSection T a) (Limits.pullback.fst T.hom A.scheme.hom)).app B.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (A.familyPointSection_fst T a)).app B.sheaf ≪≫
    (Scheme.Modules.pullbackId T.left).app B.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
