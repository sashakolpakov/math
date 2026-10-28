import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import Mathlib.RingTheory.Etale.Pi
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Multiplicative Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeDual.Construction

noncomputable section

/-!
The Cartier coordinates of a diagonalizable group are the function ring
on its labels. This proves etaleness of the complementary opposite
factor without discarding the nonreduced original multiplicative group.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry WithConv
open scoped _root_.CategoryTheory.MonObj

universe u

variable (R M : Type u) [CommRing R] [CommGroup M]

local notation "D" => OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate R (MonoidAlgebra R M)
local instance : CommRing D := LinearMap.convCommRing
local instance : Algebra R D := LinearMap.convAlgebra

/-- Evaluation on the group-like basis identifies the dual coordinate
algebra with all functions on the labels. -/
def diagonalizableDualCoordinatesEquiv : D ≃ₐ[R] (M → R) where
  toFun f m := f (MonoidAlgebra.single m 1)
  invFun f := toConv ((MonoidAlgebra.basis M R).constr R f)
  left_inv f := by
    apply WithConv.ofConv_injective
    exact (MonoidAlgebra.basis M R).constr_self R f.ofConv
  right_inv f := by
    funext m
    exact (MonoidAlgebra.basis M R).constr_basis R f m
  map_mul' f g := by
    funext m
    change (f * g) (MonoidAlgebra.single m 1) =
      f (MonoidAlgebra.single m 1) * g (MonoidAlgebra.single m 1)
    simp [LinearMap.convMul_apply]
  map_add' f g := by funext m; rfl
  commutes' r := by
    funext m
    change r * Coalgebra.counit (R := R) (MonoidAlgebra.single m 1) = r
    simp

def diagonalizableCartierCoordinates [Finite M] :
    CartierModel.Construction.CartierCoordinates (.of R) (CartierDuality.Characters.Construction.affineHopfGroupScheme R (MonoidAlgebra R M)) where
  algebra := CommHopfAlgCat.of R (MonoidAlgebra R M)
  finite := inferInstance
  projective := inferInstance
  cocommutative := inferInstance
  comparison := Iso.refl _

/-- The entire dual scheme is etale, with its actual representing
scheme and independently reconstructed character group law. -/
theorem diagonalizableCartierDual_etale [Finite M] :
    Etale (diagonalizableCartierCoordinates R M).dualGroup.X.hom := by
  have : Algebra.Etale R (M → R) := inferInstance
  have : Algebra.Etale R D := Algebra.Etale.of_equiv (diagonalizableDualCoordinatesEquiv R M).symm
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap R D)))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MultiplicativeDual.Construction
