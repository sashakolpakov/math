import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End

/-! # Point Evaluation CM -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM.CM

noncomputable section

/-! Evaluation of genuine algebraic group endomorphisms on geometric
points is a faithful ring action for reduced separated groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G]

def pointAction : AbelianScheme.TateComparison.End.IntegralEnd G →+* AddMonoid.End (Additive (Geometric.PointExt.CM.pointBase k ⟶ G)) where
  toFun f := (f.app (.op (Geometric.PointExt.CM.pointBase k))).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem pointAction_injective [IsReduced G.left]
    [LocallyOfFiniteType G.hom] [IsSeparated G.hom] :
    Function.Injective (pointAction G) := by
  intro f g h
  apply AbelianScheme.TateComparison.End.endSchemeMap_injective G
  apply Geometric.PointExt.CM.over_hom_ext_on_points
  intro p
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G f _ p).symm.trans
    ((congrArg (fun e : AddMonoid.End (Additive (Geometric.PointExt.CM.pointBase k ⟶ G)) =>
      (e (Additive.ofMul p)).toMul) h).trans
        (AbelianScheme.TateComparison.End.endSchemeMap_points G g _ p))

theorem end_eq_zero_of_points [IsReduced G.left]
    [LocallyOfFiniteType G.hom] [IsSeparated G.hom]
    (f : AbelianScheme.TateComparison.End.IntegralEnd G)
    (h : ∀ x, pointAction G f x = 0) : f = 0 := by
  apply pointAction_injective G
  apply AddMonoidHom.ext
  intro x
  exact h x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluationCM.CM
