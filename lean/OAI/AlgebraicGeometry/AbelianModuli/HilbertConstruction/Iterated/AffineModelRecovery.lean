import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DescendedTensorMapComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels

/-! # Affine Model Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.AffineModelRecovery

noncomputable section

/-! Explicit recovery isomorphisms for two successive coefficient extensions. -/

open TensorProduct

universe u

variable {C R A A₀ : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing A₀]
variable [Algebra C R] [Algebra R A] [Algebra C A₀]

def iteratedCoefficientAlgebra (D : Subalgebra C R) (F : Subalgebra D R) : CommAlgCat.{u} F :=
  CommAlgCat.of F (F ⊗[D] (D ⊗[C] A₀))

def iteratedCoefficientArrow {B₀ : Type u} [CommRing B₀] [Algebra C B₀]
    (D : Subalgebra C R) (F : Subalgebra D R) (ψ : D ⊗[C] A₀ →ₐ[D] D ⊗[C] B₀) :
    iteratedCoefficientAlgebra (A₀ := A₀) D F →ₐ[F] iteratedCoefficientAlgebra (A₀ := B₀) D F :=
  Algebra.TensorProduct.map (AlgHom.id F F) ψ

def iteratedCoefficientCancel (D : Subalgebra C R) (F : Subalgebra D R) :
    R ⊗[F] iteratedCoefficientAlgebra (A₀ := A₀) D F ≃ₐ[R] R ⊗[D] (D ⊗[C] A₀) :=
  Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := D ⊗[C] A₀) F

theorem iteratedCoefficientCancel_natural {B₀ : Type u} [CommRing B₀] [Algebra C B₀]
    (D : Subalgebra C R) (F : Subalgebra D R) (ψ : D ⊗[C] A₀ →ₐ[D] D ⊗[C] B₀) :
    (iteratedCoefficientCancel (A₀ := B₀) D F).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R R) (iteratedCoefficientArrow D F ψ)) =
    (Algebra.TensorProduct.map (AlgHom.id R R) ψ).comp
      (iteratedCoefficientCancel (A₀ := A₀) D F).toAlgHom :=
  Coefficient.BaseChangeComparison.coefficientBaseChangeIso_natural F ψ

def iteratedCoefficientRecovery (D : Subalgebra C R) (F : Subalgebra D R)
    (e : A ≃ₐ[R] R ⊗[C] A₀) : A ≃ₐ[R] R ⊗[F] iteratedCoefficientAlgebra (A₀ := A₀) D F :=
  (e.trans (Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A₀) D).symm).trans
    (iteratedCoefficientCancel (A₀ := A₀) D F).symm

theorem iteratedCoefficientRecovery_cancel (D : Subalgebra C R) (F : Subalgebra D R)
    (e : A ≃ₐ[R] R ⊗[C] A₀) (a : A) :
    iteratedCoefficientCancel D F (iteratedCoefficientRecovery D F e a) =
      (Coefficient.BaseChangeComparison.coefficientBaseChangeIso D).symm (e a) := by
  change iteratedCoefficientCancel D F ((iteratedCoefficientCancel D F).symm
    ((Coefficient.BaseChangeComparison.coefficientBaseChangeIso D).symm (e a))) = _
  exact (iteratedCoefficientCancel D F).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.AffineModelRecovery
