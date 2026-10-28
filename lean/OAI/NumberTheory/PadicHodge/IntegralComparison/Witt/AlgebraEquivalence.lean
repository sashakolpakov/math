import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor

/-! # Algebra Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.AlgebraEquivalence

noncomputable section

/-! Actual algebra equivalences lift functorially to Witt-vector algebra equivalences. -/

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def map (e : A ≃ₐ[R] B) : WittVector p A ≃ₐ[WittVector p R] WittVector p B where
  __ := PeriodInvariants.WittAlgebraFunctor.map p R e.toAlgHom
  invFun := PeriodInvariants.WittAlgebraFunctor.map p R e.symm.toAlgHom
  left_inv w := by
    apply WittVector.ext
    intro n
    exact e.symm_apply_apply (w.coeff n)
  right_inv w := by
    apply WittVector.ext
    intro n
    exact e.apply_symm_apply (w.coeff n)

theorem coeff (e : A ≃ₐ[R] B) (w : WittVector p A) (n : ℕ) :
    (map p R e w).coeff n = e (w.coeff n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.AlgebraEquivalence
