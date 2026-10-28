import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis

/-! # Coordinate Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateTransport

noncomputable section

/-! Transport polynomial étale coordinates along an actual algebra
isomorphism, retaining the original base algebra and parameter differentials. -/

universe u
variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  (e : A ≃ₐ[R] B)

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ R) B :=
  (e.toRingHom.comp (algebraMap (MvPolynomial σ R) A)).toAlgebra

def polynomialEquiv :
    letI := polynomialAlgebra R A B σ e
    A ≃ₐ[MvPolynomial σ R] B := by
  letI := polynomialAlgebra R A B σ e
  exact { e.toRingEquiv with commutes' := fun _ => rfl }

theorem tower :
    letI := polynomialAlgebra R A B σ e
    IsScalarTower R (MvPolynomial σ R) B := by
  let := polynomialAlgebra R A B σ e
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R B r = e (algebraMap (MvPolynomial σ R) A (algebraMap R (MvPolynomial σ R) r))
  rw [← IsScalarTower.algebraMap_apply R (MvPolynomial σ R) A]
  exact (e.commutes r).symm

omit [IsScalarTower R (MvPolynomial σ R) A] in
theorem formallyEtale [Algebra.FormallyEtale (MvPolynomial σ R) A] :
    letI := polynomialAlgebra R A B σ e
    Algebra.FormallyEtale (MvPolynomial σ R) B := by
  let := polynomialAlgebra R A B σ e
  exact Algebra.FormallyEtale.of_equiv (polynomialEquiv R A B σ e)

omit [IsScalarTower R (MvPolynomial σ R) A] in
theorem etale [Algebra.Etale (MvPolynomial σ R) A] :
    letI := polynomialAlgebra R A B σ e
    Algebra.Etale (MvPolynomial σ R) B := by
  let := polynomialAlgebra R A B σ e
  exact Algebra.Etale.of_equiv (polynomialEquiv R A B σ e)

variable [Algebra.FormallyEtale (MvPolynomial σ R) A]

def basis : Module.Basis σ B Ω[B⁄R] := by
  letI := polynomialAlgebra R A B σ e
  letI := tower R A B σ e
  letI := formallyEtale R A B σ e
  exact CoordinateFormBasis.kaehlerBasis R B σ

theorem basis_apply (i : σ) :
    basis R A B σ e i =
      KaehlerDifferential.D R B (e (algebraMap (MvPolynomial σ R) A (MvPolynomial.X i))) := by
  let := polynomialAlgebra R A B σ e
  let := tower R A B σ e
  let := formallyEtale R A B σ e
  exact CoordinateFormBasis.kaehlerBasis_apply R B σ i

theorem basis_apply_of_coordinates (x : σ → A)
    (hx : ∀ i, algebraMap (MvPolynomial σ R) A (MvPolynomial.X i) = x i) (i : σ) :
    basis R A B σ e i = KaehlerDifferential.D R B (e (x i)) := by
  rw [basis_apply, hx]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateTransport
