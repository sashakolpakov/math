import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Chow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TargetGraphRestriction

/-! # Source Chow -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.SourceChow

noncomputable section

/-! The full projection identity with integral source and arbitrary
target follows by factoring through its unique target component. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

theorem chow {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver)
    (m n p q s : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hd : q + n = s + m) (a : ProperCycleLinearity.ChowQ Y p) (b : ProperCycleLinearity.ChowQ X q) :
    ChowPushforwardMap.map f m n (p + q) (p + s) (by omega)
      (General.GeneralChowIntersection.chowMap X m p q (General.ChowPullback.pull P f m n p a) b) =
      General.GeneralChowIntersection.chowMap Y n p s a (ChowPushforwardMap.map f m n q s hd b) := by
  let C := ComponentFactor.component (Z := X.carrier) Y f.left
  let V := (Y.componentVariety C).presentation
  let i : V.toOver ⟶ Y.toOver := Component.Image.inclusion Y C
  let g : X.toOver ⟶ V.toOver := ComponentFactor.overMap Y f
  let Q := ProductRestriction.Target.presentation P i
  let : SmoothOfRelativeDimension n V.structureMap := Component.Image.component_relativeDimension Y n C
  have hfac : g ≫ i = f := ComponentFactor.overMap_fac Y f
  have hpush (t u : ℕ) (ht : t + n = u + m) (c : ProperCycleLinearity.ChowQ X t) :
      ChowPushforwardMap.map f m n t u ht c = ChowPushforwardMap.map i n n u u rfl (ChowPushforwardMap.map g m n t u ht c) := by
    rw [ChowPushforwardComposition.comp, hfac]
  have hpull : General.ChowPullback.pull P f m n p a =
      General.ChowPullback.pull Q g m n p (General.ClopenChow.restrictMap i n p a) := by
    rw [← hfac]
    exact General.TargetGraphRestriction.pull P i g m n p a
  rw [hpush (p + q) (p + s), hpush q s, General.ClopenChow.intersection i n p s, hpull]
  exact congrArg (ChowPushforwardMap.map i n n (p + s) (p + s) rfl)
    (Chow.Projection.chow Q g m n p q s hd (General.ClopenChow.restrictMap i n p a) b)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.SourceChow
