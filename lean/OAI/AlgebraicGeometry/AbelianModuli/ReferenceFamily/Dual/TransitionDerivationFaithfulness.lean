import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws

/-! # Transition Derivation Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationFaithfulness

noncomputable section

/-! Derivation coefficients faithfully recover tensor-product
automorphisms that induce the identity on the prescribed reduction. -/

open scoped TensorProduct

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

local instance dualTransitionDerivationFaithfulness_tensorCommRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem dualTensorTransitionDerivation_congr
    (e f : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u)
    (hf : ∀ u, TensorReduction.dualTensorReduction k A (f u) = TensorReduction.dualTensorReduction k A u) (h : e = f) :
    TransitionDerivationLaws.dualTensorTransitionDerivation e he = TransitionDerivationLaws.dualTensorTransitionDerivation f hf := by
  subst f
  rfl

theorem dualTensorTransitionCoordinates_injective :
    Function.Injective (CoefficientLiftTensorMap.dualTensorTransitionCoordinates (k := k) (A := A)) := by
  intro e f h
  apply AlgEquiv.ext
  intro u
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  apply C.injective
  have hu := AlgEquiv.congr_fun h (C u)
  change C (e (C.symm (C u))) = C (f (C.symm (C u))) at hu
  simpa only [C.symm_apply_apply] using hu

theorem dualTensorTransitionCoordinates_refl :
    CoefficientLiftTensorMap.dualTensorTransitionCoordinates (AlgEquiv.refl :
      (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro u
  exact (NumberCoefficients.dualTensorCoefficientEquiv k A).apply_symm_apply u

theorem dualTensorTransitionDerivation_refl :
    TransitionDerivationLaws.dualTensorTransitionDerivation (AlgEquiv.refl :
      (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) (fun _ => rfl) = 0 := by
  apply Derivation.ext
  intro a
  change (CoefficientLiftTensorMap.dualTensorTransitionCoordinates (AlgEquiv.refl :
    (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) (TrivSqZeroExt.inl a)).snd = 0
  rw [dualTensorTransitionCoordinates_refl]
  rfl

theorem dualTensorTransitionDerivation_faithful
    (e f : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (he : ∀ u, TensorReduction.dualTensorReduction k A (e u) = TensorReduction.dualTensorReduction k A u)
    (hf : ∀ u, TensorReduction.dualTensorReduction k A (f u) = TensorReduction.dualTensorReduction k A u)
    (h : TransitionDerivationLaws.dualTensorTransitionDerivation e he = TransitionDerivationLaws.dualTensorTransitionDerivation f hf) : e = f := by
  apply dualTensorTransitionCoordinates_injective
  apply AlgEquiv.coe_toAlgHom_injective
  exact TransitionDerivationLaws.dualReductionIdentity_ext (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates f).toAlgHom
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he) (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction f hf)
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps e) (CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps f) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationFaithfulness
