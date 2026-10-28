import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SummandPolynomial
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Summand Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM

noncomputable section

/-! Construct FrobeniusSlope's operators on the exact coefficient field and
generalized Hecke summand selected by GeometricComparison. Their polynomial, commutation,
and generalized eigenvalues follow from the ambient operators. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SummandPolynomial.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)
  (hcomm : ∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k))
  (χ : H → AlgebraicClosure ℚ_[q]) (L : NumberTheory.PadicHodge.GeometricComparison.Linear.FiniteHeckeCoefficientField q χ)

include hcomm

local instance summandAddCommGroup : AddCommGroup (A.deRhamHeckeSummand ρ χ L) :=
  (A.deRhamHeckeSummand ρ χ L).addCommGroup

local instance summandModule : Module L.field (A.deRhamHeckeSummand ρ χ L) :=
  (A.deRhamHeckeSummand ρ χ L).module

local instance summandEndRing : Ring (Module.End L.field (A.deRhamHeckeSummand ρ χ L)) :=
  Module.End.instRing (R := L.field) (N₁ := A.deRhamHeckeSummand ρ χ L)

local instance closureEndRing : Ring (Module.End (AlgebraicClosure ℚ_[q])
    ((AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L))) :=
  Module.End.instRing (R := AlgebraicClosure ℚ_[q])
    (N₁ := (AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L))

theorem coefficient_hecke_commute (h k : H) :
    Commute ((A.deRhamHecke ρ h).baseChange L.field)
      ((A.deRhamHecke ρ k).baseChange L.field) :=
  (hcomm h k).map (Module.End.baseChangeHom ℚ_[q] L.field A.DeRham)

def summandHecke (h : H) : Module.End L.field (A.deRhamHeckeSummand ρ χ L) :=
  NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character
    (coefficient_hecke_commute A ρ hcomm χ L) h

@[simp] theorem summandHecke_apply (h : H) (x : A.deRhamHeckeSummand ρ χ L) :
    (summandHecke A ρ hcomm χ L h x : L.field ⊗[ℚ_[q]] A.DeRham) =
      (A.deRhamHecke ρ h).baseChange L.field (x : L.field ⊗[ℚ_[q]] A.DeRham) := rfl

theorem summandHecke_commute (h k : H) :
    Commute (summandHecke A ρ hcomm χ L h) (summandHecke A ρ hcomm χ L k) :=
  SummandPolynomial.CM.restrictedHecke_commute _ L.character (coefficient_hecke_commute A ρ hcomm χ L) h k

theorem summandFrobenius_commute
    (f : Module.End ℚ_[q] A.DeRham)
    (fS : (A.deRhamHeckeSummand ρ χ L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χ L))
    (hincl : ∀ x : A.deRhamHeckeSummand ρ χ L,
      (fS x : L.field ⊗[ℚ_[q]] A.DeRham) = NumberTheory.PadicHodge.GeometricComparison.Linear.coefficientFrobenius L.field f
        (x : L.field ⊗[ℚ_[q]] A.DeRham))
    (hfcomm : ∀ h, Commute f (A.deRhamHecke ρ h)) (h : H) :
    Commute fS.toLinearMap (summandHecke A ρ hcomm χ L h) :=
  SummandPolynomial.CM.restrictedFrobenius_commute _ L.character (coefficient_hecke_commute A ρ hcomm χ L)
    (f.baseChange L.field) fS.toLinearMap hincl
    (fun k => (hfcomm k).map (Module.End.baseChangeHom ℚ_[q] L.field A.DeRham)) h

theorem summand_polynomial
    (f : Module.End ℚ_[q] A.DeRham)
    (fS : (A.deRhamHeckeSummand ρ χ L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χ L))
    (hincl : ∀ x : A.deRhamHeckeSummand ρ χ L,
      (fS x : L.field ⊗[ℚ_[q]] A.DeRham) = NumberTheory.PadicHodge.GeometricComparison.Linear.coefficientFrobenius L.field f
        (x : L.field ⊗[ℚ_[q]] A.DeRham))
    (idx : Fin 3 → H) (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f (fun i => A.deRhamHecke ρ (idx i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue (R := Module.End L.field (A.deRhamHeckeSummand ρ χ L))
      q fS.toLinearMap (fun i => summandHecke A ρ hcomm χ L (idx i)) = 0 :=
  SummandPolynomial.CM.restricted_polynomial _ L.character (coefficient_hecke_commute A ρ hcomm χ L) q
    (f.baseChange L.field) fS.toLinearMap hincl idx
    (SummandPolynomial.CM.polynomial_baseChange q L.field f (fun i => A.deRhamHecke ρ (idx i)) hp)

/-- These are the actual restricted Hecke pullbacks, extended to the
specified algebraic closure. -/
def closureHecke (h : H) : Module.End (AlgebraicClosure ℚ_[q])
    ((AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L)) :=
  (summandHecke A ρ hcomm χ L h).baseChange (AlgebraicClosure ℚ_[q])

theorem closureHecke_commute (h k : H) :
    Commute (closureHecke A ρ hcomm χ L h) (closureHecke A ρ hcomm χ L k) :=
  (summandHecke_commute A ρ hcomm χ L h k).map
    (Module.End.baseChangeHom L.field (AlgebraicClosure ℚ_[q]) (A.deRhamHeckeSummand ρ χ L))

theorem closureHecke_eigenvalue [FiniteDimensional ℚ_[q] A.DeRham] (h : H) :
    (closureHecke A ρ hcomm χ L h).genEigenspace (χ h) ⊤ = ⊤ := by
  change Module.End.genEigenspace ((summandHecke A ρ hcomm χ L h).baseChange (AlgebraicClosure ℚ_[q]))
    (algebraMap L.field (AlgebraicClosure ℚ_[q]) (L.character h)) ⊤ = ⊤
  exact NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.baseChange_generalized_eigenvalue (L := L.field) (V := A.deRhamHeckeSummand ρ χ L)
    (AlgebraicClosure ℚ_[q]) (summandHecke A ρ hcomm χ L h) (L.character h)
    (NumberTheory.PadicHodge.ScalarExtension.CM.ExtremeSlopesAdapter.restrictedHecke_generalized_eigenvalue
      (fun k => (A.deRhamHecke ρ k).baseChange L.field) L.character
      (coefficient_hecke_commute A ρ hcomm χ L) h)

variable (f : Module.End ℚ_[q] A.DeRham)
  (fS : (A.deRhamHeckeSummand ρ χ L) ≃ₗ[L.field] (A.deRhamHeckeSummand ρ χ L))
  (hincl : ∀ x : A.deRhamHeckeSummand ρ χ L,
    (fS x : L.field ⊗[ℚ_[q]] A.DeRham) = NumberTheory.PadicHodge.GeometricComparison.Linear.coefficientFrobenius L.field f
      (x : L.field ⊗[ℚ_[q]] A.DeRham))

include hincl

theorem closureFrobenius_commute (hfcomm : ∀ h, Commute f (A.deRhamHecke ρ h)) (h : H) :
    Commute (fS.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])) (closureHecke A ρ hcomm χ L h) :=
  (summandFrobenius_commute A ρ hcomm χ L f fS hincl hfcomm h).map
    (Module.End.baseChangeHom L.field (AlgebraicClosure ℚ_[q]) (A.deRhamHeckeSummand ρ χ L))

theorem closure_polynomial (idx : Fin 3 → H)
    (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f (fun i => A.deRhamHecke ρ (idx i)) = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue (R := Module.End (AlgebraicClosure ℚ_[q])
      ((AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L)))
      q (fS.toLinearMap.baseChange (AlgebraicClosure ℚ_[q]))
      (fun i => closureHecke A ρ hcomm χ L (idx i)) = 0 :=
  SummandPolynomial.CM.polynomial_baseChange (F := L.field) (V := A.deRhamHeckeSummand ρ χ L)
    q (AlgebraicClosure ℚ_[q]) fS.toLinearMap (fun i => summandHecke A ρ hcomm χ L (idx i))
    (summand_polynomial A ρ hcomm χ L f fS hincl idx hp)

theorem operators_on_native_summand
    [FiniteDimensional ℚ_[q] A.DeRham]
    (hfcomm : ∀ h, Commute f (A.deRhamHecke ρ h))
    (idx : Fin 3 → H) (hp : Ordinary.Polynomial.CM.heckePolynomialValue q f (fun i => A.deRhamHecke ρ (idx i)) = 0) :
    let T := fun i => closureHecke A ρ hcomm χ L (idx i)
    let F : Module.End (AlgebraicClosure ℚ_[q])
      ((AlgebraicClosure ℚ_[q]) ⊗[L.field] (A.deRhamHeckeSummand ρ χ L)) :=
      fS.toLinearMap.baseChange (AlgebraicClosure ℚ_[q])
    (∀ i j, Commute (T i) (T j)) ∧ (∀ i, Commute F (T i)) ∧
    Ordinary.Polynomial.CM.heckePolynomialValue q F T = 0 ∧
    (∀ i, (T i).genEigenspace (χ (idx i)) ⊤ = ⊤) :=
  ⟨fun i j => closureHecke_commute A ρ hcomm χ L (idx i) (idx j),
    fun i => closureFrobenius_commute A ρ hcomm χ L f fS hincl hfcomm (idx i),
    closure_polynomial A ρ hcomm χ L f fS hincl idx hp,
    fun i => closureHecke_eigenvalue A ρ hcomm χ L (idx i)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SummandOperators.CM
