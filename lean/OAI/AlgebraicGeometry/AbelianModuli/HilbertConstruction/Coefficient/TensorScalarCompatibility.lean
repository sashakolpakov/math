import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorMaps

/-! # Tensor Scalar Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorScalarCompatibility

noncomputable section

/-! Coefficient inclusions commute with scalar extension of algebra homomorphisms. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem coefficientTensorMap_smul (D : Subalgebra C R) (d : D) (b : D ⊗[C] B) :
    TensorMaps.coefficientTensorMap D (d • b) = (d.val : R) • TensorMaps.coefficientTensorMap D b := by
  calc
    TensorMaps.coefficientTensorMap D (d • b) =
        TensorMaps.coefficientTensorMap D ((algebraMap D (D ⊗[C] B)) d * b) :=
      congrArg (TensorMaps.coefficientTensorMap D) (Algebra.smul_def d b)
    _ = TensorMaps.coefficientTensorMap D ((algebraMap D (D ⊗[C] B)) d) * TensorMaps.coefficientTensorMap D b :=
      map_mul (TensorMaps.coefficientTensorMap D) _ _
    _ = (algebraMap R (R ⊗[C] B)) d.val * TensorMaps.coefficientTensorMap D b := rfl
    _ = (d.val : R) • TensorMaps.coefficientTensorMap D b := (Algebra.smul_def d.val _).symm

theorem coefficientTensorMap_liftEquiv (D : Subalgebra C R)
    (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B) (ψ : A →ₐ[C] D ⊗[C] B)
    (hψ : (TensorMaps.coefficientTensorMap D).comp ψ = (AlgHom.liftEquiv C R A (R ⊗[C] B)).symm φ)
    (x : D ⊗[C] A) :
    TensorMaps.coefficientTensorMap D ((AlgHom.liftEquiv C D A (D ⊗[C] B)) ψ x) =
      φ (TensorMaps.coefficientTensorMap D x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul d a =>
    change TensorMaps.coefficientTensorMap D (d • ψ a) = φ ((d.val : R) ⊗ₜ[C] a)
    rw [coefficientTensorMap_smul]
    have ha : TensorMaps.coefficientTensorMap D (ψ a) = φ (1 ⊗ₜ[C] a) := DFunLike.congr_fun hψ a
    rw [ha]
    calc
      (d.val : R) • φ (1 ⊗ₜ[C] a) = φ ((d.val : R) • (1 ⊗ₜ[C] a)) :=
        (φ.toLinearMap.map_smul _ _).symm
      _ = φ ((d.val : R) ⊗ₜ[C] a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.TensorScalarCompatibility
