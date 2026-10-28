import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalFrame

/-! # Vertical Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalUnits.Construction

noncomputable section

/-! The compatible vertical unit frame on every test scheme, obtained
from the uniquely normalized actual Poincare axis frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincareVerticalUnit_factor {T : Over S} (c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (hc : c ≫ snd D.abelian.scheme A.scheme = 1) :
    (c ≫ fst D.abelian.scheme A.scheme) ≫ VerticalFrame.Construction.poincareVerticalAxis D = c := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [VerticalFrame.Construction.poincareVerticalAxis, Category.assoc, lift_fst, Category.comp_id]
  · simpa only [VerticalFrame.Construction.poincareVerticalAxis, Category.assoc, lift_snd, MonObj.comp_one] using hc.symm

variable {k : Type u} [Field k] {d : ℕ} {Ab : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} (Db : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData Ab)

def poincareVerticalUnitFrame {T : Over (Spec (.of k))} (c : T ⟶ Db.abelian.scheme ⊗ Ab.scheme)
    (hc : c ≫ snd Db.abelian.scheme Ab.scheme = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) c :=
  Picard.PoincareBundle.GlobalPullbackFrame.atPoint (VerticalFrame.Construction.poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) (VerticalFrame.Construction.poincareVerticalAxisFrame Db)
    (c ≫ fst Db.abelian.scheme Ab.scheme) c (poincareVerticalUnit_factor Db c hc)

theorem poincareVerticalUnitFrame_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (c : T ⟶ Db.abelian.scheme ⊗ Ab.scheme) (c' : U ⟶ Db.abelian.scheme ⊗ Ab.scheme)
    (hc : c ≫ snd Db.abelian.scheme Ab.scheme = 1) (hc' : c' ≫ snd Db.abelian.scheme Ab.scheme = 1)
    (hr : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullSection (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) r c c' hr (poincareVerticalUnitFrame Db c hc).hom =
      (poincareVerticalUnitFrame Db c' hc').hom :=
  Picard.PoincareBundle.GlobalFrameNaturality.atPoint_section_natural (VerticalFrame.Construction.poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db)
    (VerticalFrame.Construction.poincareVerticalAxisFrame Db) r (c ≫ fst Db.abelian.scheme Ab.scheme) c
    (poincareVerticalUnit_factor Db c hc) (c' ≫ fst Db.abelian.scheme Ab.scheme) c'
    (poincareVerticalUnit_factor Db c' hc')
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ fst Db.abelian.scheme Ab.scheme) hr)) hr

theorem poincareVerticalAxisFrame_at_zero (T : Over (Spec (.of k))) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint (VerticalFrame.Construction.poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) (VerticalFrame.Construction.poincareVerticalAxisFrame Db)
      (1 : T ⟶ Db.abelian.scheme) 1 (MonObj.one_comp (VerticalFrame.Construction.poincareVerticalAxis Db)) = OriginFrames.Construction.poincareZeroFrame Db T := by
  have h := Picard.PoincareBundle.GlobalFrameNaturality.atPoint_pullback
    (VerticalFrame.Construction.poincareVerticalAxis Db) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine Db) (VerticalFrame.Construction.poincareVerticalAxisFrame Db)
    (toUnit T) η[Db.abelian.scheme] 1 (VerticalFrame.Construction.poincareVerticalAxis_origin Db)
    (1 : T ⟶ Db.abelian.scheme) 1 (MonObj.one_comp (VerticalFrame.Construction.poincareVerticalAxis Db))
    rfl (MonObj.comp_one (toUnit T))
  rw [VerticalFrame.Construction.poincareVerticalAxisFrame_at_origin] at h
  exact h.symm.trans (OriginFrames.Construction.poincareZeroFrame_natural Db (toUnit T))

theorem poincareVerticalUnitFrame_zero (T : Over (Spec (.of k))) :
    poincareVerticalUnitFrame Db (1 : T ⟶ Db.abelian.scheme ⊗ Ab.scheme)
      (MonObj.one_comp (snd Db.abelian.scheme Ab.scheme)) = OriginFrames.Construction.poincareZeroFrame Db T := by
  simpa only [poincareVerticalUnitFrame, MonObj.one_comp] using poincareVerticalAxisFrame_at_zero Db T

theorem poincareUnitFrames_agree_at_zero (T : Over (Spec (.of k))) :
    AxisFrames.Construction.poincareHorizontalUnitFrame Db (1 : T ⟶ Db.abelian.scheme ⊗ Ab.scheme)
      (MonObj.one_comp (fst Db.abelian.scheme Ab.scheme)) =
    poincareVerticalUnitFrame Db (1 : T ⟶ Db.abelian.scheme ⊗ Ab.scheme)
      (MonObj.one_comp (snd Db.abelian.scheme Ab.scheme)) :=
  (AxisFrames.Construction.poincareHorizontalUnitFrame_zero Db T).trans (poincareVerticalUnitFrame_zero Db T).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalUnits.Construction
