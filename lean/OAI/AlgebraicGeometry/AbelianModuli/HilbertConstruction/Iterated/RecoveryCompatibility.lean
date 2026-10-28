import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveryComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.AffineModelRecovery

/-! # Recovery Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.RecoveryCompatibility

noncomputable section

/-! The final iterated recovery isomorphisms identify descended arrows with the original arrows. -/

open TensorProduct

universe u

theorem iteratedCoefficientRecovery_map
    {C R A B A₀ B₀ : Type u}
    [CommRing C] [CommRing R] [CommRing A] [CommRing B] [CommRing A₀] [CommRing B₀]
    [Algebra C R] [Algebra R A] [Algebra R B] [Algebra C A₀] [Algebra C B₀]
    (D : Subalgebra C R) (F : Subalgebra D R)
    (eA : A ≃ₐ[R] R ⊗[C] A₀) (eB : B ≃ₐ[R] R ⊗[C] B₀) (φ : A →ₐ[R] B)
    (ψ : D ⊗[C] A₀ →ₐ[D] D ⊗[C] B₀)
    (h : ∀ x, Coefficient.TensorMaps.coefficientTensorMap D (ψ x) =
      Affine.ModelConjugation.modelConjugateMap eA eB φ (Coefficient.TensorMaps.coefficientTensorMap D x)) (a : A) :
    AffineModelRecovery.iteratedCoefficientRecovery D F eB (φ a) =
      Algebra.TensorProduct.map (AlgHom.id R R)
        (AffineModelRecovery.iteratedCoefficientArrow D F ψ) (AffineModelRecovery.iteratedCoefficientRecovery D F eA a) := by
  let eDA := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A₀) D
  let eDB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B₀) D
  let eFA := AffineModelRecovery.iteratedCoefficientCancel (A₀ := A₀) D F
  let eFB := AffineModelRecovery.iteratedCoefficientCancel (A₀ := B₀) D F
  let p := Algebra.TensorProduct.map (AlgHom.id R R) ψ
  let q := Algebra.TensorProduct.map (AlgHom.id R R) (AffineModelRecovery.iteratedCoefficientArrow D F ψ)
  have hd (z : R ⊗[D] (D ⊗[C] A₀)) :
      eDB (p z) = Affine.ModelConjugation.modelConjugateMap eA eB φ (eDA z) :=
    DFunLike.congr_fun (DescendedTensorMapComparison.descended_tensorMap_comparison D (Affine.ModelConjugation.modelConjugateMap eA eB φ) ψ h) z
  have hf (z : R ⊗[F] AffineModelRecovery.iteratedCoefficientAlgebra (A₀ := A₀) D F) : eFB (q z) = p (eFA z) :=
    DFunLike.congr_fun (AffineModelRecovery.iteratedCoefficientCancel_natural D F ψ) z
  apply eFB.injective
  calc
    eFB (AffineModelRecovery.iteratedCoefficientRecovery D F eB (φ a)) = eDB.symm (eB (φ a)) :=
      AffineModelRecovery.iteratedCoefficientRecovery_cancel D F eB (φ a)
    _ = p (eDA.symm (eA a)) := by
      apply eDB.injective
      rw [eDB.apply_symm_apply, hd, eDA.apply_symm_apply, Affine.ModelConjugation.modelConjugateMap_recovery]
    _ = p (eFA (AffineModelRecovery.iteratedCoefficientRecovery D F eA a)) :=
      congrArg p (AffineModelRecovery.iteratedCoefficientRecovery_cancel D F eA a).symm
    _ = eFB (q (AffineModelRecovery.iteratedCoefficientRecovery D F eA a)) := (hf _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.RecoveryCompatibility
