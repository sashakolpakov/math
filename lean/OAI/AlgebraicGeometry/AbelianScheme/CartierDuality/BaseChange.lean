import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DualAlgebra

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BaseChange.Construction

noncomputable section

/-!
# CartierDuality: base change of the complete dual Hopf structure

The comparison with the scalar-extended dual preserves comultiplication and
counit as well as multiplication. The scalar extension is arbitrary.
-/

open _root_.Module TensorProduct Coalgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (S : Type w) [CommRing S] [Algebra R S]
variable (A : Type v) [CommRing A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
variable [Module.Finite R A] [Module.Projective R A]

local instance e56BaseChangeInstance1 : CommRing (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convCommRing
local instance e56BaseChangeInstance2 : Algebra R (DualAlgebra.Construction.DualCoordinate R A) := LinearMap.convAlgebra
local instance e56BaseChangeInstance3 : CommRing (S ⊗[R] DualAlgebra.Construction.DualCoordinate R A) := Algebra.TensorProduct.instCommRing
local instance e56BaseChangeInstance4 : CommRing (DualAlgebra.Construction.DualCoordinate S (S ⊗[R] A)) := LinearMap.convCommRing
local instance e56BaseChangeInstance5 : Algebra S (DualAlgebra.Construction.DualCoordinate S (S ⊗[R] A)) := LinearMap.convAlgebra

omit [Coalgebra.IsCocomm R A] in
theorem dualCoordinateBaseChange_comul_eval
    (s t u : S) (f : DualAlgebra.Construction.DualCoordinate R A) (x y : A) :
    DualAlgebra.Construction.dualCoordinateTensorEquiv S (S ⊗[R] A) (S ⊗[R] A)
      (TensorProduct.map (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S).toLinearMap
        (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S).toLinearMap
          (Coalgebra.comul (R := S) (s ⊗ₜ[R] f)))
      ((t ⊗ₜ[R] x) ⊗ₜ[S] (u ⊗ₜ[R] y)) =
        s * t * u * algebraMap R S (f (x * y)) := by
  let ρ := Coalgebra.Repr.arbitrary R f
  have hsum : ∑ i ∈ ρ.index, ρ.left i x * ρ.right i y = f (x * y) := by
    rw [← DualAlgebra.Construction.dualCoordinateComul_apply R A f x y]
    change _ = DualAlgebra.Construction.dualCoordinateTensorEquiv R A A (Coalgebra.comul f) (x ⊗ₜ[R] y)
    rw [← ρ.eq]
    simp
  rw [← (DualAlgebra.Construction.scalarExtensionRepr R S (DualAlgebra.Construction.DualCoordinate R A) ρ s).eq]
  simp only [map_sum, LinearMap.sum_apply, DualAlgebra.Construction.scalarExtensionRepr,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, DualAlgebra.Construction.dualCoordinateTensorEquiv_apply,
    DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv_apply, one_mul]
  simp only [← map_mul, ← Finset.mul_sum, ← map_sum, mul_assoc, mul_left_comm, mul_comm,
    hsum]

/-- Arbitrary base change commutes with Cartier duality as a bialgebra
isomorphism, hence also with its induced group-scheme structure. -/
def dualCoordinateBaseChangeBialgEquiv :
    S ⊗[R] DualAlgebra.Construction.DualCoordinate R A ≃ₐc[S] DualAlgebra.Construction.DualCoordinate S (S ⊗[R] A) where
  __ := DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S
  map_mul' := DualAlgebra.Construction.dualCoordinateBaseChange_mul R S A
  counit_comp := by
    apply AlgebraTensorModule.ext
    intro s f
    change DualAlgebra.Construction.dualCoordinateCounit S (S ⊗[R] A)
      (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S (s ⊗ₜ[R] f)) =
        Coalgebra.counit (R := S) (s ⊗ₜ[R] f)
    rw [DualAlgebra.Construction.dualCoordinateCounit_apply, Algebra.TensorProduct.one_def,
      DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv_apply]
    rw [TensorProduct.counit_tmul]
    change s * 1 * algebraMap R S (f 1) = (f 1) • s
    simp [Algebra.smul_def, mul_comm]
  map_comp_comul := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s f =>
    apply (DualAlgebra.Construction.dualCoordinateTensorEquiv S (S ⊗[R] A) (S ⊗[R] A)).injective
    apply TensorProduct.ext'
    intro p q
    induction p using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul t x =>
    induction q using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul u y =>
    change DualAlgebra.Construction.dualCoordinateTensorEquiv S (S ⊗[R] A) (S ⊗[R] A)
      (TensorProduct.map (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S).toLinearMap
        (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S).toLinearMap
          (Coalgebra.comul (R := S) (s ⊗ₜ[R] f)))
      ((t ⊗ₜ[R] x) ⊗ₜ[S] (u ⊗ₜ[R] y)) = _
    rw [dualCoordinateBaseChange_comul_eval]
    change _ = DualAlgebra.Construction.dualCoordinateTensorEquiv S (S ⊗[R] A) (S ⊗[R] A)
      (DualAlgebra.Construction.dualCoordinateComul S (S ⊗[R] A)
        (DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv R A S (s ⊗ₜ[R] f)))
      ((t ⊗ₜ[R] x) ⊗ₜ[S] (u ⊗ₜ[R] y))
    rw [DualAlgebra.Construction.dualCoordinateComul_apply, Algebra.TensorProduct.tmul_mul_tmul,
      DualAlgebra.Construction.dualCoordinateBaseChangeLinearEquiv_apply]
    simp only [mul_assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BaseChange.Construction
