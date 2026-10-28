import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints

/-! # Group Base Change Identity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GroupBaseChangeIdentity

noncomputable section

/-! Literal identity sections commute with the actual group-scheme
base-change projection. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S T : Scheme.{u}} (A : Over S) [GrpObj A] (b : T ⟶ S)

theorem projection :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback b).obj A).left ≫ pullback.fst A.hom b =
      b ≫ (1 : Over.mk (𝟙 S) ⟶ A).left := by
  have h := congrArg Over.Hom.left
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints.groupBaseChangePointsMulEquiv A b (Over.mk (𝟙 T))).map_one
  change (1 : Over.mk (𝟙 T) ⟶ (Over.pullback b).obj A).left ≫ pullback.fst A.hom b =
    (1 : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ A).left at h
  let v : (Over.map b).obj (Over.mk (𝟙 T)) ⟶ Over.mk (𝟙 S) :=
    Over.homMk b (by simp)
  have hv := congrArg Over.Hom.left (MonObj.comp_one v (M := A))
  exact h.trans hv.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GroupBaseChangeIdentity
