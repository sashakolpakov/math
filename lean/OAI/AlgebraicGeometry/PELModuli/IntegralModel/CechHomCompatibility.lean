import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullHomCommonFactor

/-! # Cech Hom Compatibility -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility

noncomputable section

/-! Equality on the actual cartesian double overlap implies compatibility
on every test scheme, retaining the native module-pullback comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent

theorem compatibleHom_of_cartesian_overlap
    {X Y V : Scheme.{0}} (f : X ⟶ Y) (a b : V ⟶ X) (H : IsPullback a b f f)
    {M N : Y.Modules}
    (q : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (s : V ⟶ Y) (ha : a ≫ f = s) (hb : b ≫ f = s)
    (h : Isogenies.NeighborCounting.FramedPullback.pullbackHomTo a f s ha q = Isogenies.NeighborCounting.FramedPullback.pullbackHomTo b f s hb q) :
    Isogenies.NeighborCounting.FramedDescent.CompatibleHom f q := by
  intro T x y p hx hy
  let c := H.lift x y (hx.trans hy.symm)
  have hca : c ≫ a = x := H.lift_fst _ _ _
  have hcb : c ≫ b = y := H.lift_snd _ _ _
  have hcp : c ≫ s = p := (congrArg (c ≫ ·) ha.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hca).trans hx))
  exact Isogenies.NeighborCounting.PullHomCommonFactor.native_common_factor f q a b s ha hb h
    c x y p hca hcb hcp hx hy

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechHomCompatibility
