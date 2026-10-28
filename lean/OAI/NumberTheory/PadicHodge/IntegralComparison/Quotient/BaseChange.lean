import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.BaseChange

noncomputable section

/-! Native quotient base change and the canonical map on Kahler differentials. -/

open scoped TensorProduct

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A] (I : Ideal R)

instance pushout : Algebra.IsPushout R (R ⧸ I) A (A ⧸ I.map (algebraMap R A)) where
  out := IsBaseChange.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm.toLinearEquiv
    (fun a => (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm_apply_eq.mpr
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A I a).symm)

def differentials :
    (A ⧸ I.map (algebraMap R A)) ⊗[A] KaehlerDifferential R A ≃ₗ[A ⧸ I.map (algebraMap R A)]
      KaehlerDifferential (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
  KaehlerDifferential.tensorKaehlerEquiv R (R ⧸ I) A (A ⧸ I.map (algebraMap R A))

theorem differentials_tmul_D (a b : A) : differentials R A I
    (Ideal.Quotient.mk (I.map (algebraMap R A)) a ⊗ₜ[A] KaehlerDifferential.D R A b) =
      Ideal.Quotient.mk (I.map (algebraMap R A)) a •
        KaehlerDifferential.D (R ⧸ I) (A ⧸ I.map (algebraMap R A))
          (Ideal.Quotient.mk (I.map (algebraMap R A)) b) :=
  KaehlerDifferential.tensorKaehlerEquiv_tmul_D R (R ⧸ I) A (A ⧸ I.map (algebraMap R A)) _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.BaseChange
