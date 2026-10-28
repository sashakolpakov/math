import OAI.AlgebraicGeometry.GroupSchemes.Cartier
import OAI.AlgebraicGeometry.GroupSchemes.LocalObstruction

/-! # Dual Points -/

namespace OAI.AlgebraicGeometry.GroupSchemes.DualPoints.FiniteEtale

noncomputable section

/-! Rational Cartier-dual points as elements of the original coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra

/-- A dual rational point determines its element of the coordinate algebra by biduality. -/
def pointElement : WithConv (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₐ[k] k) →* A where
  toFun f := (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A).symm (toConv f.ofConv.toLinearMap)
  map_one' := by
    rw [AlgHom.toLinearMap_convOne, map_one]
  map_mul' f g := by
    rw [AlgHom.toLinearMap_convMul, map_mul]

/-- Distinct dual rational points give distinct coordinate elements. -/
theorem pointElement_injective : Function.Injective (pointElement k A) := by
  intro f g h
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  exact (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A).symm.injective h

/-- A dual rational point has augmentation one in the original coordinate algebra. -/
theorem pointElement_counit (f : WithConv (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₐ[k] k)) :
    Coalgebra.counit (R := k) (pointElement k A f) = 1 := by
  change Coalgebra.counit (R := k)
    ((AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A).symm (toConv f.ofConv.toLinearMap)) = 1
  rw [CoalgHomClass.counit_comp_apply]
  exact f.ofConv.map_one

/-- The dual rational points of a local rank-p coordinate algebra are p-torsion. -/
theorem dual_points_pow (p : ℕ) [Fact p.Prime] [CharP k p] [IsLocalRing A]
    (hdim : Module.finrank k A = p) (f : WithConv (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₐ[k] k)) :
    f ^ p = 1 := by
  apply pointElement_injective k A
  rw [(pointElement k A).map_pow f p, (pointElement k A).map_one]
  rw [LocalObstruction.FiniteEtale.frobenius_of_local_rank_prime k A p hdim
    (Bialgebra.counitAlgHom k A), Bialgebra.counitAlgHom_apply, pointElement_counit,
    one_pow, map_one]

/-- The dual point calculation applies to the actual Cartier-dual group scheme. -/
theorem dualOfHopf_points_pow (p : ℕ) [Fact p.Prime] [CharP k p] [IsLocalRing A]
    (hdim : Module.finrank k A = p)
    (x : FiniteEtale.affine k (CommAlgCat.of k k) ⟶ (FiniteEtale.FiniteCommGroupScheme.dualOfHopf (k := k) A).scheme) :
    x ^ p = 1 := by
  let e := @Spec.mapMulEquiv k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) k _ _ _ inferInstance _
  have h := dual_points_pow k A p hdim (e.symm x)
  have he : e (e.symm x) ^ p = 1 :=
    (map_pow e (e.symm x) p).symm.trans ((congrArg e h).trans e.map_one)
  exact (congrArg (fun y => y ^ p) (e.apply_symm_apply x)).symm.trans he

end

end OAI.AlgebraicGeometry.GroupSchemes.DualPoints.FiniteEtale
