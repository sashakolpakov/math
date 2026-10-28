import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FamilyTriviality

/-! # Zero Family Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual Cartesian Poincare family is trivial exactly for the dual zero section, on every test scheme, including nonreduced schemes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)

theorem Dual.Data.DualAbelianData.poincareBaseFamily_zero_implies_trivial
    {T P : Scheme.{u}} (t : T ⟶ D.abelian.scheme.left)
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
    (ht : t = (t ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left) :
    Nonempty ((D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule P) := by
  let T' := Over.mk (t ≫ D.abelian.scheme.hom)
  let x : T' ⟶ D.abelian.scheme := Over.homMk t rfl
  have hx : x = 1 := by
    apply Over.OverMorphism.ext
    change t = (t ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left
    exact ht
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
  let L := D.poincare.pullback a
  let e : (Scheme.Modules.pullback E.hom).obj L.sheaf ≅ (D.poincareAt x).sheaf :=
    (Scheme.Modules.pullbackComp E.hom a).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr he).app D.poincare.sheaf
  obtain ⟨et⟩ := (D.poincareAt_trivial_iff x).mpr hx
  let u := e ≪≫ et
  let v : (Scheme.Modules.pullback E.inv).obj ((Scheme.Modules.pullback E.hom).obj L.sheaf) ≅
      L.sheaf :=
    (Scheme.Modules.pullbackComp E.inv E.hom).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr E.inv_hom_id).app L.sheaf ≪≫
      (Scheme.Modules.pullbackId P).app L.sheaf
  exact ⟨v.symm ≪≫ (Scheme.Modules.pullback E.inv).mapIso u ≪≫
    Line.Bundles.structureModulePullbackIso E.inv⟩

theorem Dual.Data.DualAbelianData.poincareBaseFamily_trivial_iff_zero
    {T P : Scheme.{u}} (t : T ⟶ D.abelian.scheme.left)
    {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t) :
    Nonempty ((D.poincare.pullback a).sheaf ≅ Line.Bundles.structureModule P) ↔
      t = (t ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left :=
  ⟨D.poincareBaseFamily_trivial_implies_zero t H, D.poincareBaseFamily_zero_implies_trivial t H⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
