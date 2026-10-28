import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCancellation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced

/-! # Finite Kernel Cancellation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.FiniteKernelCancellation

noncomputable section

/-! Finite-kernel cancellation for actual abelian varieties over the
original field, reflected from their geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

variable {k : Type} [Field k] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {Y Z : Over (Spec (.of k))} [GrpObj Y] [GrpObj Z]
  (f : Y ⟶ Z) [IsMonHom f] [IsFinite f.left]
  (a b : A.scheme ⟶ Y) [IsMonHom a] [IsMonHom b]

theorem cancel_finite_group_map (hab : a ≫ f = b ≫ f) : a = b := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let F := Over.pullback s
  have : F.Faithful := Picard.PoincareBundle.Field.Extension.pullback_faithful s
  have : IsReduced (F.obj A.scheme).left := by
    change IsReduced (A.pullback s).scheme.left
    exact ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field (A.pullback s).scheme.hom
  have : ConnectedSpace (F.obj A.scheme).left := by
    change ConnectedSpace (A.pullback s).scheme.left
    exact GeometricallyConnected.connectedSpace_of_subsingleton (A.pullback s).scheme.hom
  have : LocallyOfFiniteType (F.obj A.scheme).hom :=
    inferInstanceAs (LocallyOfFiniteType (A.pullback s).scheme.hom)
  have : IsFinite (F.map f).left := MorphismProperty.overPullbackMap (P := @IsFinite) s f inferInstance
  apply F.map_injective
  apply AbelianScheme.FrobeniusKernel.FiniteCancellation.Construction.cancel_finite_group_map (F.map f) (F.map a) (F.map b)
  exact (F.map_comp a f).symm.trans ((congrArg F.map hab).trans (F.map_comp b f))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.FiniteKernelCancellation
