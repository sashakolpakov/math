import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearScalarFactorization
import Mathlib.Algebra.Algebra.Basic

/-! # Compatible Algebra Equiv -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CompatibleAlgebraEquiv

/-! # Compatible ring equivalences give the required semilinear module equivalence -/

attribute [local instance] SemilinearScalarFactorization.forwardPair
  SemilinearScalarFactorization.backwardPair

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] (e : R ≃+* S) (E : A ≃+* B)
  (h : ∀ r : R, E (algebraMap R A r) = algebraMap S B (e r))

def equiv : A ≃ₛₗ[e.toRingHom] B where
  __ := E.toAddEquiv
  map_smul' r x := by
    change E (r • x) = e r • E x
    rw [Algebra.smul_def, map_mul, h, Algebra.smul_def]

theorem equiv_apply (x : A) : equiv e E h x = E x := rfl

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CompatibleAlgebraEquiv
