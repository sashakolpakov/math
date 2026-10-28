import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Surjective Quotient Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurjectiveQuotientBaseChange

noncomputable section

/-! Base change of a surjective algebra is its actual quotient by the
extended kernel ideal. This identification does not require flatness. -/

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

variable (R A S : Type u) [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

def equiv (h : Function.Surjective (algebraMap R A)) :
    S ⊗[R] A ≃ₗ[S] S ⧸ (RingHom.ker (algebraMap R A)).map (algebraMap R S) :=
  (LinearEquiv.baseChange R S A (R ⧸ RingHom.ker (algebraMap R A))
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) h).toLinearEquiv.symm).trans
    (Ideal.qoutMapEquivTensorQout (R := R) (I := RingHom.ker (algebraMap R A)) S).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurjectiveQuotientBaseChange
