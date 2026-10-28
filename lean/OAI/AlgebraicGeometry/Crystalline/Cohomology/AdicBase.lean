import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Adic Base -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicBase.AdicBaseQuotients

noncomputable section

/-! # The module and ring quotients for an extended adic ideal -/

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (J : Ideal A) (hIJ : I.map (algebraMap R A) = J)

include hIJ in
theorem filtration (n : ℕ) :
    I ^ n • (⊤ : Submodule R A) = (J ^ n).restrictScalars R := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow, hIJ]

def quotientEquiv (n : ℕ) :
    (A ⧸ (I ^ n • (⊤ : Submodule R A))) ≃ₗ[R] (A ⧸ J ^ n) :=
  (Submodule.quotEquivOfEq _ _ (filtration I J hIJ n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R _)

theorem quotientEquiv_mk (n : ℕ) (a : A) :
    quotientEquiv I J hIJ n (Submodule.Quotient.mk a) = Ideal.Quotient.mk (J ^ n) a := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]
  rfl

theorem transition (m n : ℕ) (h : m ≤ n) (x : A ⧸ (I ^ n • (⊤ : Submodule R A))) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (quotientEquiv I J hIJ n x) =
      quotientEquiv I J hIJ m (AdicCompletion.transitionMap I A h x) := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [quotientEquiv_mk]
    exact (quotientEquiv_mk I J hIJ m a).symm

theorem inverse_transition (m n : ℕ) (h : m ≤ n) (x : A ⧸ J ^ n) :
    AdicCompletion.transitionMap I A h ((quotientEquiv I J hIJ n).symm x) =
      (quotientEquiv I J hIJ m).symm (Ideal.Quotient.factor (Ideal.pow_le_pow_right h) x) := by
  apply (quotientEquiv I J hIJ m).injective
  rw [LinearEquiv.apply_symm_apply, ← transition, LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicBase.AdicBaseQuotients
