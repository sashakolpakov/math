import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointSectionTranslation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Bundles

/-! # Point Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Evaluating a Poincare bundle at a pair of test-scheme points and its unit normalizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

def Dual.Data.DualAbelianData.poincarePair (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) : Line.Bundles.LineBundle T.left :=
  (D.poincareAt f).pullback (A.familyPointSection T a)

theorem Dual.Data.DualAbelianData.poincarePair_map (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    A.familyPointSection T a ≫ (Picard.PicardSheaf.familySchemeFunctor A.scheme).map f = (lift f a).left := by
  have h : lift (𝟙 T) a ≫ (f ▷ A.scheme) = lift f a := by
    simp only [lift_whiskerRight, Category.id_comp]
  exact congrArg Over.Hom.left h

def Dual.Data.DualAbelianData.poincarePairDirectIso (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) (a : T ⟶ A.scheme) :
    (D.poincarePair f a).sheaf ≅ (D.poincare.pullback (lift f a).left).sheaf :=
  (Scheme.Modules.pullbackComp (A.familyPointSection T a) ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (D.poincarePair_map f a)).app D.poincare.sheaf

def Dual.Data.DualAbelianData.poincarePair_one_right (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) : (D.poincarePair f 1).sheaf ≅ Line.Bundles.structureModule T.left :=
  D.poincareAt_zeroIso f

def Dual.Data.DualAbelianData.poincarePair_one_left (D : Dual.Data.DualAbelianData A) {T : Over S}
    (a : T ⟶ A.scheme) : (D.poincarePair 1 a).sheaf ≅ Line.Bundles.structureModule T.left := by
  have h : (lift (1 : T ⟶ D.abelian.scheme) a).left =
      a.left ≫ (lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).left := by
    have he : lift (1 : T ⟶ D.abelian.scheme) a =
        a ≫ lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme) := by
      simp only [comp_lift, MonObj.comp_one, Category.comp_id]
    exact congrArg Over.Hom.left he
  exact D.poincarePairDirectIso 1 a ≪≫
    (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp a.left (lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).left).symm.app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback a.left).mapIso D.normalizedAtDualZero.some ≪≫ Line.Bundles.structureModulePullbackIso a.left

def Dual.Data.DualAbelianData.poincarePairGraphIso (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) :
    (D.poincarePair p (𝟙 A.scheme)).sheaf ≅ (PoincareGraph.Bundles.poincareGraphBundle D p).sheaf :=
  D.poincarePairDirectIso p (𝟙 A.scheme)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
