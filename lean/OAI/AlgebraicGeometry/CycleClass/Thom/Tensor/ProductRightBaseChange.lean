import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra
import Mathlib.RingTheory.Flat.Stability

/-! # Product Right Base Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightBaseChange.Constructions

noncomputable section

/-! Base changing the right factor of a tensor algebra preserves
flatness. The proof exhibits the actual tensor cancellation as an
equivalence over the source tensor algebra. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R P S : Type u) [CommRing k] [CommRing R] [CommRing P] [CommRing S]
  [Algebra k R] [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def baseChangeMap : R ⊗[k] P →ₐ[R] R ⊗[k] S :=
  Algebra.TensorProduct.map (AlgHom.id R R) (IsScalarTower.toAlgHom k P S)

def cancel : (R ⊗[k] P) ⊗[P] S ≃ₐ[k] R ⊗[k] S :=
  ((((Algebra.TensorProduct.congr (ProductRightAlgebra.Constructions.rightSwap k R P) (AlgEquiv.refl : S ≃ₐ[P] S)).trans
    (Algebra.TensorProduct.comm P (P ⊗[k] R) S)).trans
      (Algebra.TensorProduct.cancelBaseChange k P P S R)).restrictScalars k).trans
        (Algebra.TensorProduct.comm k S R)

theorem cancel_tmul (r : R) (p : P) (s : S) :
    cancel k R P S ((r ⊗ₜ[k] p) ⊗ₜ[P] s) = r ⊗ₜ[k] (p • s) := by
  simp only [cancel, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, ProductRightAlgebra.Constructions.rightSwap_tmul,
    AlgEquiv.coe_refl, id_eq, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul]

theorem cancel_algebraMap (b : R ⊗[k] P) :
    cancel k R P S (algebraMap (R ⊗[k] P) ((R ⊗[k] P) ⊗[P] S) b) = baseChangeMap k R P S b := by
  induction b using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r p =>
    change cancel k R P S ((r ⊗ₜ[k] p) ⊗ₜ[P] 1) = r ⊗ₜ[k] algebraMap P S p
    rw [cancel_tmul, Algebra.smul_def, mul_one]

local instance baseChangeAlgebra : Algebra (R ⊗[k] P) (R ⊗[k] S) :=
  (baseChangeMap k R P S).toRingHom.toAlgebra

def baseChangeEquiv : (R ⊗[k] P) ⊗[P] S ≃ₐ[R ⊗[k] P] R ⊗[k] S where
  __ := (cancel k R P S).toRingEquiv
  commutes' := cancel_algebraMap k R P S

theorem flat [Module.Flat P S] : Module.Flat (R ⊗[k] P) (R ⊗[k] S) :=
  Module.Flat.of_linearEquiv (baseChangeEquiv k R P S).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightBaseChange.Constructions
