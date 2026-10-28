import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.CohomologyCup

/-! # Product Congruence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.ProductCongruence.CohomologyCup

noncomputable section

/-! Identical cochain products give identical products on native
cohomology, independently of the proof of the product rule. -/

universe u v

variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{v} R) ℕ)
  (μ ν : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m))
  (hμ : ∀ n m (x : K.X n) (y : K.X m),
    K.d (n + m) (n + m + 1) (μ n m x y) =
      CohomologyCup.cupInto K μ (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
      (-1 : ℤ) ^ n • CohomologyCup.cupInto K μ n (m + 1) (n + m + 1) (by omega) x (K.d m (m + 1) y))
  (hν : ∀ n m (x : K.X n) (y : K.X m),
    K.d (n + m) (n + m + 1) (ν n m x y) =
      CohomologyCup.cupInto K ν (n + 1) m (n + m + 1) (by omega) (K.d n (n + 1) x) y +
      (-1 : ℤ) ^ n • CohomologyCup.cupInto K ν n (m + 1) (n + m + 1) (by omega) x (K.d m (m + 1) y))

theorem cohomologyCup_congr (h : μ = ν) (p q : ℕ) :
    CohomologyCup.cohomologyCup K μ hμ p q = CohomologyCup.cohomologyCup K ν hν p q := by
  subst ν
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.ProductCongruence.CohomologyCup
