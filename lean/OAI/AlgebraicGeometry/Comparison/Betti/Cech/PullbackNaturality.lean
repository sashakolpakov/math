import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

/-! # Pullback Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackNaturality

noncomputable section

/-! Squares of the original coefficient maps induce squares of the actual pullback Čech maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)
    {F F' : TopCat.Sheaf AddCommGrpCat.{0} X} {G G' : TopCat.Sheaf AddCommGrpCat.{0} Y}
    (a : F ⟶ F') (b : G ⟶ G')
    (α : F.obj ⟶ (Opens.map f).op ⋙ G.obj) (β : F'.obj ⟶ (Opens.map f).op ⋙ G'.obj)

theorem additiveCechPullbackMap_square
    (h : a.hom ≫ β = α ≫ Functor.whiskerLeft (Opens.map f).op b.hom) :
    (cechComplexFunctor U).map a.hom ≫ PullbackGlobalIsomorphism.additiveCechPullbackMap f U F' G' β =
      PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G α ≫
        (cechComplexFunctor (fun i => (Opens.map f).obj (U i))).map b.hom := by
  let C := cechComplexFunctor (A := AddCommGrpCat.{0}) U
  let D := cechComplexFunctor (A := AddCommGrpCat.{0}) (fun i => (Opens.map f).obj (U i))
  let e := (AdditiveCechImage.additiveCechDirectImageIso f U G.obj).hom
  let e' := (AdditiveCechImage.additiveCechDirectImageIso f U G'.obj).hom
  let c := Functor.whiskerLeft (Opens.map f).op b.hom
  have hm : C.map a.hom ≫ C.map β = C.map α ≫ C.map c :=
    (C.map_comp a.hom β).symm.trans ((congrArg C.map h).trans (C.map_comp α c))
  have he : C.map c ≫ e' = e ≫ D.map b.hom := AdditiveCechImage.additiveCechDirectImageIso_naturality f U b.hom
  change C.map a.hom ≫ (C.map β ≫ e') = (C.map α ≫ e) ≫ D.map b.hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e') hm).trans
    ((Category.assoc _ _ _).trans ((congrArg (C.map α ≫ ·) he).trans (Category.assoc _ _ _).symm)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackNaturality
