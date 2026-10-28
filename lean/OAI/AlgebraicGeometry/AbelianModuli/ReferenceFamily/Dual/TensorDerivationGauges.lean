import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws

/-! # Tensor Derivation Gauges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorDerivationGauges

noncomputable section

/-! Derivation gauges act on the actual tensor product over the complete
dual-number base, preserve reduction, and have the prescribed coefficients. -/

open scoped TensorProduct

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

local instance dualTensorDerivationGauges_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

def dualTensorDerivationGauge (d : Derivation k A A) :
    (DualNumber k ⊗[k] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A) := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  let e : (DualNumber k ⊗[k] A) ≃ₐ[k] (DualNumber k ⊗[k] A) :=
    C.trans ((Dual.Derivation.dualDerivationAutomorphism d).trans C.symm)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro c
  apply C.injective
  change C (C.symm (Dual.Derivation.dualDerivationAutomorphism d
    (C (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) c)))) =
      C (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) c)
  rw [C.apply_symm_apply, CoefficientLiftTensorMap.dualTensorCoefficientEquiv_base]
  apply TrivSqZeroExt.ext
  · rfl
  · change d (algebraMap k A c.fst) + algebraMap k A c.snd = algebraMap k A c.snd
    rw [d.map_algebraMap, zero_add]

theorem dualTensorDerivationGauge_reduction (d : Derivation k A A) (u : DualNumber k ⊗[k] A) :
    TensorReduction.dualTensorReduction k A (dualTensorDerivationGauge d u) = TensorReduction.dualTensorReduction k A u := by
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  change (C (C.symm (Dual.Derivation.dualDerivationAutomorphism d (C u)))).fst = (C u).fst
  rw [C.apply_symm_apply]
  rfl

theorem dualTensorDerivationGauge_coordinates (d : Derivation k A A) :
    CoefficientLiftTensorMap.dualTensorTransitionCoordinates (dualTensorDerivationGauge d) = Dual.Derivation.dualDerivationAutomorphism d := by
  apply AlgEquiv.ext
  intro u
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  change C (C.symm (Dual.Derivation.dualDerivationAutomorphism d (C (C.symm u)))) = Dual.Derivation.dualDerivationAutomorphism d u
  rw [C.apply_symm_apply, C.apply_symm_apply]

theorem dualTensorDerivationGauge_derivation (d : Derivation k A A) :
    TransitionDerivationLaws.dualTensorTransitionDerivation (dualTensorDerivationGauge d) (dualTensorDerivationGauge_reduction d) = d := by
  apply Derivation.ext
  intro a
  rw [TransitionDerivationLaws.dualTensorTransitionDerivation_apply, dualTensorDerivationGauge_coordinates]
  change d a + 0 = d a
  exact add_zero _

theorem dualTensorDerivationGauge_zero :
    dualTensorDerivationGauge (0 : Derivation k A A) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro u
  let C := NumberCoefficients.dualTensorCoefficientEquiv k A
  change C.symm (Dual.Derivation.dualDerivationAutomorphism (0 : Derivation k A A) (C u)) = u
  rw [Dual.Derivation.dualDerivationAutomorphism_zero]
  exact C.symm_apply_apply u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorDerivationGauges
