import Mathlib.RingTheory.Bialgebra.Basic

/-! # Coalgebra Tensor Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraTensorMaps

/-! Algebra compatibility for the tensor maps used in a cocycle twist. -/

universe u v

open Coalgebra TensorProduct

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Bialgebra k R]

theorem comul_rTensor_mul (x y : R ⊗[k] R) :
    (comul (R := k) (A := R)).rTensor R (x * y) =
      (comul (R := k) (A := R)).rTensor R x * (comul (R := k) (A := R)).rTensor R y :=
  (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k R) (.id k R)).map_mul x y

theorem comul_lTensor_mul (x y : R ⊗[k] R) :
    (comul (R := k) (A := R)).lTensor R (x * y) =
      (comul (R := k) (A := R)).lTensor R x * (comul (R := k) (A := R)).lTensor R y :=
  (Algebra.TensorProduct.map (.id k R) (Bialgebra.comulAlgHom k R)).map_mul x y

theorem counit_rTensor_mul (x y : R ⊗[k] R) :
    (counit (R := k) (A := R)).rTensor R (x * y) =
      (counit (R := k) (A := R)).rTensor R x * (counit (R := k) (A := R)).rTensor R y :=
  (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k R) (.id k R)).map_mul x y

theorem counit_lTensor_mul (x y : R ⊗[k] R) :
    (counit (R := k) (A := R)).lTensor R (x * y) =
      (counit (R := k) (A := R)).lTensor R x * (counit (R := k) (A := R)).lTensor R y :=
  (Algebra.TensorProduct.map (.id k R) (Bialgebra.counitAlgHom k R)).map_mul x y

omit [Bialgebra k R] in
theorem assoc_mul [Algebra k R] (x y : (R ⊗[k] R) ⊗[k] R) :
    TensorProduct.assoc k R R R (x * y) =
      TensorProduct.assoc k R R R x * TensorProduct.assoc k R R R y :=
  (Algebra.TensorProduct.assoc k k k R R R).map_mul x y

omit [Bialgebra k R] in
theorem comm_mul [Algebra k R] (x y : R ⊗[k] R) :
    TensorProduct.comm k R R (x * y) =
      TensorProduct.comm k R R x * TensorProduct.comm k R R y :=
  (Algebra.TensorProduct.comm k R R).map_mul x y

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraTensorMaps
