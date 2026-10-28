import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Coordinate Differentials -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.CoordinateDifferentials

noncomputable section

/-! A genuine polynomial coordinate algebra equivalence gives the basis
of differentials of its actual coordinate functions. -/

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C]
  {σ : Type w} (e : C ≃ₐ[R] MvPolynomial σ R)

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ R) C := e.symm.toRingHom.toAlgebra

theorem tower :
    letI := polynomialAlgebra e
    IsScalarTower R (MvPolynomial σ R) C := by
  let := polynomialAlgebra e
  exact IsScalarTower.of_algebraMap_eq (fun r => (e.symm.commutes r).symm)

theorem formallyEtale :
    letI := polynomialAlgebra e
    Algebra.FormallyEtale (MvPolynomial σ R) C := by
  let := polynomialAlgebra e
  let f : MvPolynomial σ R ≃ₐ[MvPolynomial σ R] C :=
    { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  exact Algebra.FormallyEtale.of_equiv f

def basis : Module.Basis σ C Ω[C⁄R] := by
  letI := polynomialAlgebra e
  letI := tower e
  letI := formallyEtale e
  exact ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange C).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) C)

theorem basis_apply (j : σ) : basis e j = KaehlerDifferential.D R C (e.symm (MvPolynomial.X j)) := by
  let := polynomialAlgebra e
  let := tower e
  let := formallyEtale e
  rw [basis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact ((LinearEquiv.symm_apply_eq
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) C)).mp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R (MvPolynomial σ R) C
      (MvPolynomial.X j))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.CoordinateDifferentials
