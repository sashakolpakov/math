import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses

/-! # Point Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every Poincare bundle classified by a dual-valued point is trivial along the abelian zero section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.familyZeroSection (T : Over S) : T.left ⟶ (Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T :=
  (lift (𝟙 T) (1 : T ⟶ A.scheme)).left

theorem Abelian.Schemes.AbelianScheme.familyZeroSection_fst (T : Over S) :
    A.familyZeroSection T ≫ Limits.pullback.fst T.hom A.scheme.hom = 𝟙 T.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A.scheme))

theorem Abelian.Schemes.AbelianScheme.familyZeroSection_natural {T U : Over S} (f : T ⟶ U) :
    A.familyZeroSection T ≫ (Picard.PicardSheaf.familySchemeFunctor A.scheme).map f = f.left ≫ A.familyZeroSection U := by
  have h : lift (𝟙 T) (1 : T ⟶ A.scheme) ≫ (f ▷ A.scheme) =
      f ≫ lift (𝟙 U) (1 : U ⟶ A.scheme) := by
    simp only [lift_whiskerRight, comp_lift, Category.id_comp, Category.comp_id, MonObj.comp_one]
  exact congrArg Over.Hom.left h

variable {A}

def Dual.Data.DualAbelianData.poincareAt_zeroIso (D : Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) :
    ((D.poincareAt f).pullback (A.familyZeroSection T)).sheaf ≅ Line.Bundles.structureModule T.left :=
  (Scheme.Modules.pullbackComp (A.familyZeroSection T) ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (A.familyZeroSection_natural f)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp f.left (A.familyZeroSection D.abelian.scheme)).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback f.left).mapIso D.normalizedAtAbelianZero.some ≪≫
    Line.Bundles.structureModulePullbackIso f.left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
