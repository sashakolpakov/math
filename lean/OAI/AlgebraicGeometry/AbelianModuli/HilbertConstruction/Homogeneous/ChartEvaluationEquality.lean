import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

/-! # Chart Evaluation Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationEquality

noncomputable section

/-! Two homogeneous-chart evaluations agree when their homogeneous
numerators satisfy the cross-multiplication identities. -/
universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type v} [CommRing A]

theorem homogeneousAwayEvaluation_eq_of_cross
    (g : ℕ → Submodule R S) [GradedAlgebra g] (f : S) {d : ℕ} (hfd : f ∈ g d)
    (φ ψ : S →+* A) (hφ : IsUnit (φ f)) (hψ : IsUnit (ψ f))
    (hcross : ∀ (k : ℕ) (p : S), p ∈ g (k • d) → φ p * ψ f ^ k = ψ p * φ f ^ k) :
    AwayEvaluation.homogeneousAwayEvaluation g f φ hφ = AwayEvaluation.homogeneousAwayEvaluation g f ψ hψ := by
  apply RingHom.ext
  intro x
  obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective g hfd x
  let x := HomogeneousLocalization.Away.mk g hfd k p hp
  have heφ := AwayEvaluation.homogeneousAwayEvaluation_mk_cross g f φ hφ hfd k p hp
  have heψ := AwayEvaluation.homogeneousAwayEvaluation_mk_cross g f ψ hψ hfd k p hp
  apply ((hφ.pow k).mul (hψ.pow k)).mul_right_cancel
  calc
    AwayEvaluation.homogeneousAwayEvaluation g f φ hφ x * (φ f ^ k * ψ f ^ k) =
        (AwayEvaluation.homogeneousAwayEvaluation g f φ hφ x * φ f ^ k) * ψ f ^ k := (mul_assoc _ _ _).symm
    _ = φ p * ψ f ^ k := by rw [heφ]
    _ = ψ p * φ f ^ k := hcross k p hp
    _ = (AwayEvaluation.homogeneousAwayEvaluation g f ψ hψ x * ψ f ^ k) * φ f ^ k := by rw [heψ]
    _ = AwayEvaluation.homogeneousAwayEvaluation g f ψ hψ x * (φ f ^ k * ψ f ^ k) := by ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationEquality
