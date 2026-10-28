import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointFaithfulness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.AtIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback

/-! # Family Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Triviality of the actual Poincare family detects the dual zero section on every test scheme, including nonreduced schemes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)

theorem Dual.Data.DualAbelianData.poincareAt_trivial_iff {T : Over S} (x : T ⟶ D.abelian.scheme) :
    Nonempty ((D.poincareAt x).sheaf ≅ Line.Bundles.structureModule ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) ↔
      x = 1 := by
  constructor
  · rintro ⟨e⟩
    apply D.poincareAt_class_injective T
    exact Quotient.sound ⟨e ≪≫ (D.poincareAt_oneIso T).symm⟩
  · rintro rfl
    exact ⟨D.poincareAt_oneIso T⟩

theorem Dual.Data.DualAbelianData.poincareBaseFamily_trivial_implies_zero
    {T P : Scheme.{u}} (t : T ⟶ D.abelian.scheme.left)
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
    (hL : Nonempty ((D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule P)) :
    t = (t ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left := by
  let T' := Over.mk (t ≫ D.abelian.scheme.hom)
  let x : T' ⟶ D.abelian.scheme := Over.homMk t rfl
  let HF : IsPullback ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map x)
      (pullback.fst T'.hom A.scheme.hom)
      (pullback.fst D.abelian.scheme.hom A.scheme.hom) t :=
    Picard.TestFamilyPullback.familySchemeFunctor_map_isPullback A.scheme x
  let E : (Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T' ≅ P := HF.isoPullback ≪≫ H.isoPullback.symm
  have he : E.hom ≫ a = (Picard.PicardSheaf.familySchemeFunctor A.scheme).map x := by
    change (HF.isoPullback.hom ≫ H.isoPullback.inv) ≫ a = _
    exact (Category.assoc HF.isoPullback.hom H.isoPullback.inv a).trans
      ((congrArg (fun v : pullback (pullback.fst D.abelian.scheme.hom A.scheme.hom) t ⟶
          (D.abelian.scheme ⊗ A.scheme).left => HF.isoPullback.hom ≫ v)
        H.isoPullback_inv_fst).trans HF.isoPullback_hom_fst)
  let e : ((D.poincare.pullback a).pullback E.hom).sheaf ≅ (D.poincareAt x).sheaf :=
    (Scheme.Modules.pullbackComp E.hom a).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr he).app D.poincare.sheaf
  obtain ⟨htriv⟩ := hL
  have hx : x = 1 := (D.poincareAt_trivial_iff x).mp ⟨e.symm ≪≫
    (Scheme.Modules.pullback E.hom).mapIso htriv ≪≫ Line.Bundles.structureModulePullbackIso E.hom⟩
  have h := congrArg Over.Hom.left hx
  rw [Hom.one_def] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
