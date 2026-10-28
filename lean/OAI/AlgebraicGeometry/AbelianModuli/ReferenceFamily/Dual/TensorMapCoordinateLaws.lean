import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality

/-! # Tensor Map Coordinate Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinateLaws

noncomputable section

/-! The literal dual-tensor coefficient comparison preserves original
map composition, transition maps, and undeformed coefficient maps. -/

open scoped TensorProduct

variable {k A B C : Type} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]

theorem dualTensorMapCoordinates_comp
    (f : (DualNumber k ⊗[k] A) →ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (g : (DualNumber k ⊗[k] B) →ₐ[DualNumber k] (DualNumber k ⊗[k] C)) :
    TensorMapCoordinates.dualTensorMapCoordinates (g.comp f) = (TensorMapCoordinates.dualTensorMapCoordinates g).comp (TensorMapCoordinates.dualTensorMapCoordinates f) := by
  apply AlgHom.ext
  intro u
  change NumberCoefficients.dualTensorCoefficientEquiv k C (g (f ((NumberCoefficients.dualTensorCoefficientEquiv k A).symm u))) =
    NumberCoefficients.dualTensorCoefficientEquiv k C (g ((NumberCoefficients.dualTensorCoefficientEquiv k B).symm
      (NumberCoefficients.dualTensorCoefficientEquiv k B (f ((NumberCoefficients.dualTensorCoefficientEquiv k A).symm u)))))
  rw [AlgEquiv.symm_apply_apply]

theorem dualTensorMapCoordinates_equiv
    (f : (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A)) :
    TensorMapCoordinates.dualTensorMapCoordinates f.toAlgHom = (CoefficientLiftTensorMap.dualTensorTransitionCoordinates f).toAlgHom := by
  apply AlgHom.ext
  intro u
  rfl

theorem dualTensorMapCoordinates_coefficient (q : A →ₐ[k] B) :
    TensorMapCoordinates.dualTensorMapCoordinates (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q) =
      NumberCoefficients.dualNumberAlgMap q := by
  apply AlgHom.ext
  intro u
  have h := TensorCoefficientNaturality.dualTensorCoefficientEquiv_natural q ((NumberCoefficients.dualTensorCoefficientEquiv k A).symm u)
  exact h.trans (congrArg (NumberCoefficients.dualNumberAlgMap q) ((NumberCoefficients.dualTensorCoefficientEquiv k A).apply_symm_apply u))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorMapCoordinateLaws
