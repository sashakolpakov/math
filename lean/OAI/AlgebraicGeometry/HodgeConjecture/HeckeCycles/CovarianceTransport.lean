import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SurjectiveRepresentationDescent

/-! # Covariance Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CovarianceTransport.CM

noncomputable section

/-! Transport an operator covariance identity through actual test and
phase equivalences, retaining the proved intertwining equations. -/

variable {V W P Q : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem transport (e : V ≃ₗ[ℂ] W) (U : V ≃ₗ[ℂ] V) (T : W ≃ₗ[ℂ] W)
    (ha : ∀ x, e (U x) = T (e x))
    (H : P → V →ₗ[ℂ] V) (K : Q → W →ₗ[ℂ] W)
    (q : Q → P) (hq : Function.Surjective q)
    (hh : ∀ z x, e (H (q z) x) = K z (e x))
    (a : P → P) (b : Q → Q) (hp : ∀ z, a (q z) = q (b z))
    (hc : ∀ z x, T (K z x) = K (b z) (T x)) (v : P) (x : V) :
    U (H v x) = H (a v) (U x) := by
  obtain ⟨z, rfl⟩ := hq v
  apply e.injective
  rw [ha, hh, hc, hp, hh, ha]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CovarianceTransport.CM
