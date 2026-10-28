import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso

/-! # Level Point Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.LevelPointBaseChange

noncomputable section

/-! An equal-level native block transport has the same point map
before and after any specified base-change group comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso

local instance levelPointPullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

theorem baseChangedPointEquiv_nativeLevel {S₁ S₂ S₀ : Scheme}
    (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂) {A : Over S₁} [GrpObj A] [IsCommMonObj A]
    (n m : ℕ) (p : A ⟶ A) [IsMonHom p] (h : n = m) (H : Grp (Over S₂))
    (e : (Over.pullback f).mapGrp.obj (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock m p)) ≅
      (Over.pullback g).mapGrp.obj H)
    (a : Additive (Over.mk f ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p)) :
    GroupPointBaseChange.baseChangedPointEquiv f g _ H
      ((Over.pullback f).mapGrp.mapIso (ActiveSubspaces.IntrinsicBlockLevelGroupIso.nativeBlockLevelGroupIso n m p h) ≪≫ e) a.toMul =
    GroupPointBaseChange.baseChangedPointEquiv f g _ H e (ActiveSubspaces.nativeBlockPointLevelEquiv n m p h a).toMul := by
  subst m
  change GroupPointBaseChange.baseChangedPointEquiv f g _ H
    ((Over.pullback f).mapGrp.mapIso (Iso.refl (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p))) ≪≫ e) a.toMul =
    GroupPointBaseChange.baseChangedPointEquiv f g _ H e a.toMul
  rw [Functor.mapIso_refl, Iso.refl_trans]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.LevelPointBaseChange
