import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Characters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Naturality

/-! # Character Groups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroups.Construction

noncomputable section

/-!
# CartierDuality: Cartier character representation as a group isomorphism

The represented group law is the product of characters. This verifies the
group structure in addition to the already proved pointwise representation.
-/

open _root_.Module TensorProduct Coalgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (S : Type w) [CommRing S] [Algebra R S]
variable (A : Type v) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance e56CharacterGroupsInstance1 : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance e56CharacterGroupsInstance2 : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra

omit [Coalgebra.IsCocomm R A] in
theorem scalarExtendedDual_mul_eval {f : DualAlgebra.Construction.DualCoordinate R A} {ι : Type*}
    (ρ : Coalgebra.Repr R f ι) (z w : S ⊗[R] A) :
    f.ofConv.baseChange S (z * w) =
      ∑ i ∈ ρ.index, (ρ.left i).ofConv.baseChange S z *
        (ρ.right i).ofConv.baseChange S w := by
  have hsum (x y : A) : ∑ i ∈ ρ.index, ρ.left i x * ρ.right i y = f (x * y) := by
    rw [← DualAlgebra.Construction.dualCoordinateComul_apply R A f x y]
    change _ = DualAlgebra.Construction.dualCoordinateTensorEquiv R A A (Coalgebra.comul f) (x ⊗ₜ[R] y)
    rw [← ρ.eq]
    simp
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [add_mul, hz, hz', Finset.sum_add_distrib]
  | tmul s x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp [mul_add, hw, hw', Finset.sum_add_distrib]
    | tmul t y =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, Module.Dual.baseChange_apply_tmul,
        Algebra.smul_def]
      simp only [← map_mul, ← Finset.mul_sum, ← map_sum,
        mul_assoc, mul_left_comm, mul_comm, hsum]

theorem affineCharacterPoint_mul
    (z w : GroupLike S (S ⊗[R] A)) :
    WithConv.toConv ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm (z * w)) =
      WithConv.toConv ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm z) *
        WithConv.toConv ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm w) := by
  apply WithConv.ext
  apply AlgHom.ext
  intro f
  change (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm (z * w) f =
    (WithConv.toConv ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm z) *
      WithConv.toConv ((DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm w)) f
  rw [DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual, AlgHom.convMul_apply]
  let ρ := Coalgebra.Repr.arbitrary R f
  change f.ofConv.baseChange S (z.val * w.val) = _
  rw [scalarExtendedDual_mul_eval R S A ρ, ← ρ.eq]
  simp [DualAlgebra.Construction.affineDualPointsEquivCharacters_symm_apply_dual]

/-- Affine points of the Cartier dual and characters are isomorphic as
groups. The domain law is the scheme law defined by the dual Hopf algebra. -/
def affineDualPointsMulEquivCharacters :
    WithConv (DualAlgebra.Construction.DualCoordinate R A →ₐ[R] S) ≃* GroupLike S (S ⊗[R] A) :=
  MulEquiv.symm {
    toEquiv := (DualAlgebra.Construction.affineDualPointsEquivCharacters R S A).symm.trans {
      toFun := WithConv.toConv
      invFun := WithConv.ofConv
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    map_mul' := affineCharacterPoint_mul R S A }

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroups.Construction
