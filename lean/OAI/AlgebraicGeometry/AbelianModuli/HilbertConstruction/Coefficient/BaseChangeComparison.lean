import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapDescent

/-! # Base Change Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BaseChangeComparison

noncomputable section

/-! The coefficient inclusion agrees with the canonical iterated-base-change isomorphism. -/

open TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

def coefficientBaseChangeIso (D : Subalgebra C R) :
    R ⊗[D] (D ⊗[C] A) ≃ₐ[R] R ⊗[C] A :=
  Algebra.TensorProduct.cancelBaseChange C D R R A

theorem coefficientBaseChangeIso_one_tmul (D : Subalgebra C R) (x : D ⊗[C] A) :
    coefficientBaseChangeIso D ((1 : R) ⊗ₜ[D] x) = TensorMaps.coefficientTensorMap D x := by
  induction x using TensorProduct.inductionOn with
  | tmul d a =>
    simp only [coefficientBaseChangeIso, Algebra.TensorProduct.cancelBaseChange_tmul]
    change ((d : R) * 1) ⊗ₜ[C] a = (d : R) ⊗ₜ[C] a
    rw [mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

theorem coefficientBaseChangeIso_natural (D : Subalgebra C R) (φ : A →ₐ[C] B) :
    (coefficientBaseChangeIso (A := B) D).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R R)
        (Algebra.TensorProduct.map (AlgHom.id D D) φ)) =
    (Algebra.TensorProduct.map (AlgHom.id R R) φ).comp
      (coefficientBaseChangeIso (A := A) D).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    induction x using TensorProduct.inductionOn with
    | tmul d a =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        coefficientBaseChangeIso, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.cancelBaseChange_tmul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BaseChangeComparison
