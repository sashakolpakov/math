import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BaseChangeComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImmersionTransport

/-! # Descended Tensor Map Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorMapComparison

noncomputable section

/-! Coefficient-compatible descended maps recover the original map after iterated base change. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem coefficientBaseChangeIso_tmul (D : Subalgebra C R) (r : R) (x : D ⊗[C] A) :
    Coefficient.BaseChangeComparison.coefficientBaseChangeIso D (r ⊗ₜ[D] x) = r • Coefficient.TensorMaps.coefficientTensorMap D x := by
  have heq : r ⊗ₜ[D] x = r • ((1 : R) ⊗ₜ[D] x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  calc
    Coefficient.BaseChangeComparison.coefficientBaseChangeIso D (r ⊗ₜ[D] x) =
        Coefficient.BaseChangeComparison.coefficientBaseChangeIso D (r • ((1 : R) ⊗ₜ[D] x)) := congrArg _ heq
    _ = r • Coefficient.BaseChangeComparison.coefficientBaseChangeIso D ((1 : R) ⊗ₜ[D] x) :=
      (Coefficient.BaseChangeComparison.coefficientBaseChangeIso D).toLinearMap.map_smul r _
    _ = r • Coefficient.TensorMaps.coefficientTensorMap D x := congrArg (r • ·) (Coefficient.BaseChangeComparison.coefficientBaseChangeIso_one_tmul D x)

theorem descended_tensorMap_comparison (D : Subalgebra C R)
    (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B) (ψ : D ⊗[C] A →ₐ[D] D ⊗[C] B)
    (h : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x)) :
    (Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R R) ψ) =
    φ.comp (Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A) D).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    change Coefficient.BaseChangeComparison.coefficientBaseChangeIso D (r ⊗ₜ[D] ψ x) = φ (Coefficient.BaseChangeComparison.coefficientBaseChangeIso D (r ⊗ₜ[D] x))
    rw [coefficientBaseChangeIso_tmul, coefficientBaseChangeIso_tmul, h]
    exact (φ.toLinearMap.map_smul r _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem descended_tensorMap_isOpenImmersion (D : Subalgebra C R)
    (φ : R ⊗[C] A →ₐ[R] R ⊗[C] B) (ψ : D ⊗[C] A →ₐ[D] D ⊗[C] B)
    (h : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) = φ (Coefficient.TensorMaps.coefficientTensorMap D x))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (R := R ⊗[D] (D ⊗[C] A)) (S := R ⊗[D] (D ⊗[C] B))
      (Algebra.TensorProduct.map (AlgHom.id R R) ψ).toRingHom)) := by
  let eA := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A) D
  let eB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D
  let q := Algebra.TensorProduct.map (AlgHom.id R R) ψ
  have hw (x : R ⊗[D] (D ⊗[C] A)) : eB (q x) = φ (eA x) :=
    DFunLike.congr_fun (descended_tensorMap_comparison D φ ψ h) x
  apply Affine.ImmersionTransport.isOpenImmersion_SpecMap_of_conjugate
    (A := R ⊗[C] A) (B := R ⊗[C] B)
    (A' := R ⊗[D] (D ⊗[C] A)) (B' := R ⊗[D] (D ⊗[C] B)) φ.toRingHom q.toRingHom
    eA.symm.toRingEquiv eB.symm.toRingEquiv
  intro x
  apply eB.injective
  change eB (eB.symm (φ x)) = eB (q (eA.symm x))
  rw [eB.apply_symm_apply, hw, eA.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorMapComparison
