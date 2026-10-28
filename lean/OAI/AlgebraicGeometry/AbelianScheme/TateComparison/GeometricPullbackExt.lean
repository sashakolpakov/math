import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricExt
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELBaseChange

/-! # Geometric Pullback Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPullbackExt

noncomputable section

/-! Equality after every algebraically closed fiber pullback reflects
an actual morphism from a reduced scheme to a separated scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem over_hom_ext_geometric_pullback {S : Scheme.{u}} {X Y : Over S}
    [IsReduced X.left] [IsSeparated Y.hom] (f g : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S),
      (Over.pullback b).map f = (Over.pullback b).map g) : f = g := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  let z := pullback.lift x.left (𝟙 (Spec (.of k))) (x.w.trans (Category.id_comp b).symm)
  have hh := congrArg (fun a => z ≫ a.left ≫ pullback.fst Y.hom b) (h k b)
  rw [AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst,
    AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc, ← Category.assoc,
    pullback.lift_fst] at hh
  exact Over.OverMorphism.ext hh

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricPullbackExt
