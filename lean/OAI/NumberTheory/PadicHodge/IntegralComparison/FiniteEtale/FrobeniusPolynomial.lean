import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.WittPolynomial

/-! # Frobenius Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusPolynomial

noncomputable section

/-! A monic integer polynomial for the actual q-Frobenius on Witt vectors of a finite étale algebra. -/

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [Fintype k] [CommRing A] [Algebra k A]
  [CharP k p] [Nontrivial A] [Module.Finite k A] [Algebra.Etale k A]

def frobenius : A ≃ₐ[k] A := by
  let := PeriodInvariants.FiniteEtaleWittModule.targetCharP p k A
  let := PeriodInvariants.FiniteEtaleWittModule.targetPerfect p k A
  exact FiniteField.frobeniusAlgEquiv k A p

theorem frobenius_toAlgHom : (frobenius p k A).toAlgHom = FiniteField.frobeniusAlgHom k A := rfl

def polynomial : Polynomial ℤ := WittPolynomial.polynomial k A (frobenius p k A)

theorem monic : (polynomial p k A).Monic := WittPolynomial.monic k A _

theorem rational :
    letI := PeriodInvariants.FiniteEtaleWittModule.free p k A
    letI := PeriodInvariants.FiniteEtaleWittModule.finite p k A
    ((PeriodInvariants.WittAlgebraFunctor.map p k (FiniteField.frobeniusAlgHom k A)).toLinearMap.baseChange
      (FractionRing (WittVector p k))).charpoly =
        (polynomial p k A).map (Int.castRingHom (FractionRing (WittVector p k))) := by
  exact WittPolynomial.rational p k A (frobenius p k A)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusPolynomial
