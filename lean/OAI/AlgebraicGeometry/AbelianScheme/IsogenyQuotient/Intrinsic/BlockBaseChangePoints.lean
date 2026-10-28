import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Block Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints.Construction

noncomputable section

/-! Native torsion-block points commute with arbitrary base change.
The comparison preserves the actual inclusion in the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (p : A.scheme ⟶ A.scheme) [IsMonHom p] (n : ℕ) (b : S' ⟶ S) (U : Over S')

def nativeBlockOriginalPoint
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    (Over.map b).obj U ⟶ OppositeKernel.Construction.torsionBlock n p := by
  let e := A.baseChangePointsMulEquiv b U
  let a := x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)
  have hk : a ^ n = 1 := by
    rw [← MonObj.comp_pow, OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  have hp : a ≫ (Over.pullback b).map p = a := by
    rw [Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_supported]
  exact OppositeKernel.Construction.torsionBlockLift n p (e a)
    ((map_pow e a n).symm.trans ((congrArg e hk).trans e.map_one))
    ((AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map p b U a).symm.trans (congrArg e hp))

theorem nativeBlockOriginalPoint_inclusion
    (x : U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) :
    nativeBlockOriginalPoint A p n b U x ≫ OppositeKernel.Construction.torsionBlockInclusion n p =
      A.baseChangePointsMulEquiv b U (x ≫ OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)) := by
  unfold nativeBlockOriginalPoint
  exact OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _

theorem nativeBlockOriginalPoint_injective : Function.Injective (nativeBlockOriginalPoint A p n b U) := by
  intro x y h
  apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p))).mp
  apply (A.baseChangePointsMulEquiv b U).injective
  exact (nativeBlockOriginalPoint_inclusion A p n b U x).symm.trans
    ((congrArg (· ≫ OppositeKernel.Construction.torsionBlockInclusion n p) h).trans (nativeBlockOriginalPoint_inclusion A p n b U y))

set_option backward.isDefEq.respectTransparency false in
theorem nativeBlockOriginalPoint_surjective : Function.Surjective (nativeBlockOriginalPoint A p n b U) := by
  intro y
  let e := A.baseChangePointsMulEquiv b U
  let x := e.symm (y ≫ OppositeKernel.Construction.torsionBlockInclusion n p)
  have hx : e x = y ≫ OppositeKernel.Construction.torsionBlockInclusion n p := e.apply_symm_apply _
  have hk : x ^ n = 1 := by
    apply e.injective
    rw [map_pow, hx, e.map_one, ← MonObj.comp_pow, OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.comp_one]
  have hp : x ≫ (Over.pullback b).map p = x := by
    apply e.injective
    change A.baseChangePointsEquiv b U (x ≫ (Over.pullback b).map p) = e x
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map]
    change e x ≫ p = e x
    rw [hx, Category.assoc, OppositeKernel.Construction.torsionBlockInclusion_supported]
  refine ⟨OppositeKernel.Construction.torsionBlockLift n ((Over.pullback b).map p) x hk hp, ?_⟩
  apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp
  rw [nativeBlockOriginalPoint_inclusion, OppositeKernel.Construction.torsionBlockLift_inclusion]
  exact hx

def nativeBlockBaseChangePointsEquiv :
    (U ⟶ OppositeKernel.Construction.torsionBlock n ((Over.pullback b).map p)) ≃*
      ((Over.map b).obj U ⟶ OppositeKernel.Construction.torsionBlock n p) where
  toEquiv := Equiv.ofBijective (nativeBlockOriginalPoint A p n b U)
    ⟨nativeBlockOriginalPoint_injective A p n b U, nativeBlockOriginalPoint_surjective A p n b U⟩
  map_mul' x y := by
    change nativeBlockOriginalPoint A p n b U (x * y) =
      nativeBlockOriginalPoint A p n b U x * nativeBlockOriginalPoint A p n b U y
    apply (cancel_mono (OppositeKernel.Construction.torsionBlockInclusion n p)).mp
    rw [MonObj.mul_comp, nativeBlockOriginalPoint_inclusion, nativeBlockOriginalPoint_inclusion,
      nativeBlockOriginalPoint_inclusion]
    exact (congrArg (A.baseChangePointsMulEquiv b U)
      (MonObj.mul_comp x y (OppositeKernel.Construction.torsionBlockInclusion n ((Over.pullback b).map p)))).trans
        ((A.baseChangePointsMulEquiv b U).map_mul _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockBaseChangePoints.Construction
