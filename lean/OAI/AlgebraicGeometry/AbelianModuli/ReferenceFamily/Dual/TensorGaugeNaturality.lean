import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorDerivationGauges

/-! # Tensor Gauge Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorGaugeNaturality

noncomputable section

/-! Constructed tensor gauges preserve an actual coefficient-map square
whenever their derivations commute with that coefficient map. -/

open scoped TensorProduct

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

local instance dualTensorGaugeNaturality_sourceCommRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

local instance dualTensorGaugeNaturality_targetCommRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

theorem dualTensorDerivationGauge_coefficients (d : Derivation k A A) (u : DualNumber k ⊗[k] A) :
    NumberCoefficients.dualTensorCoefficientEquiv k A (TensorDerivationGauges.dualTensorDerivationGauge d u) =
      Dual.Derivation.dualDerivationAutomorphism d (NumberCoefficients.dualTensorCoefficientEquiv k A u) :=
  (NumberCoefficients.dualTensorCoefficientEquiv k A).apply_symm_apply _

theorem dualTensorDerivationGauge_natural (q : A →ₐ[k] B) (d : Derivation k A A) (e : Derivation k B B)
    (h : ∀ a, q (d a) = e (q a)) :
    (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q).comp
        (TensorDerivationGauges.dualTensorDerivationGauge d).toAlgHom =
      (TensorDerivationGauges.dualTensorDerivationGauge e).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q) := by
  apply AlgHom.ext
  intro u
  apply (NumberCoefficients.dualTensorCoefficientEquiv k B).injective
  change NumberCoefficients.dualTensorCoefficientEquiv k B
      (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q (TensorDerivationGauges.dualTensorDerivationGauge d u)) =
    NumberCoefficients.dualTensorCoefficientEquiv k B
      (TensorDerivationGauges.dualTensorDerivationGauge e (Algebra.TensorProduct.map (AlgHom.id (DualNumber k) (DualNumber k)) q u))
  rw [TensorCoefficientNaturality.dualTensorCoefficientEquiv_natural, dualTensorDerivationGauge_coefficients,
    dualTensorDerivationGauge_coefficients, TensorCoefficientNaturality.dualTensorCoefficientEquiv_natural]
  exact AlgHom.congr_fun (Dual.Derivation.dualDerivationAutomorphism_natural q d e h) (NumberCoefficients.dualTensorCoefficientEquiv k A u)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorGaugeNaturality
