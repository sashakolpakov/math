import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

/-! # Pull Hom Common Factor -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullHomCommonFactor

noncomputable section

/-! Equality after a common factor is preserved by the actual pullback
composition comparisons. -/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

theorem common_factor
    {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X Y V W : C} {M N : F.obj (.mk (op Y))} (f : X ⟶ Y)
    (q : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (x y : V ⟶ X) (s : V ⟶ Y) (hx : x ≫ f = s) (hy : y ≫ f = s)
    (h : pullHom q x s s hx hx = pullHom q y s s hy hy)
    (a : W ⟶ V) (u v : W ⟶ X) (p : W ⟶ Y)
    (hax : a ≫ x = u) (hay : a ≫ y = v) (has : a ≫ s = p)
    (hu : u ≫ f = p) (hv : v ≫ f = p) :
    pullHom q u p p hu hu = pullHom q v p p hv hv := by
  have hx' : (a ≫ x) ≫ f = p := by rw [hax, hu]
  have hy' : (a ≫ y) ≫ f = p := by rw [hay, hv]
  calc
    _ = pullHom q (a ≫ x) p p hx' hx' :=
      Picard.PoincareBundle.PullHom.pullHom_congr q _ _ hax.symm p p hu hu hx' hx'
    _ = pullHom (pullHom q x s s hx hx) a p p has has :=
      (pullHom_pullHom q x s s a p p hx hx has has).symm
    _ = pullHom (pullHom q y s s hy hy) a p p has has :=
      congrArg (fun r ↦ pullHom r a p p has has) h
    _ = pullHom q (a ≫ y) p p hy' hy' :=
      pullHom_pullHom q y s s a p p hy hy has has
    _ = pullHom q v p p hv hv :=
      Picard.PoincareBundle.PullHom.pullHom_congr q _ _ hay p p hy' hy' hv hv

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModulePullbackHom

theorem native_common_factor {X Y V W : Scheme.{u}} {M N : Y.Modules} (f : X ⟶ Y)
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (x y : V ⟶ X) (s : V ⟶ Y) (hx : x ≫ f = s) (hy : y ≫ f = s)
    (h : FramedPullback.pullbackHomTo x f s hx q = FramedPullback.pullbackHomTo y f s hy q)
    (a : W ⟶ V) (u v : W ⟶ X) (p : W ⟶ Y)
    (hax : a ≫ x = u) (hay : a ≫ y = v) (has : a ≫ s = p)
    (hu : u ≫ f = p) (hv : v ≫ f = p) :
    FramedPullback.pullbackHomTo u f p hu q = FramedPullback.pullbackHomTo v f p hv q := by
  have hi := (ModulePullbackHom.pullbackHomTo_eq_pullHom x f s hx q).symm.trans
    (h.trans (ModulePullbackHom.pullbackHomTo_eq_pullHom y f s hy q))
  have ho := common_factor (F := ModulePullbackHom.modulePullbackFunctor) f q x y s hx hy hi
    a u v p hax hay has hu hv
  exact (ModulePullbackHom.pullbackHomTo_eq_pullHom u f p hu q).trans
    (ho.trans (ModulePullbackHom.pullbackHomTo_eq_pullHom v f p hv q).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullHomCommonFactor
