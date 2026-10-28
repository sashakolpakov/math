import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

/-! # Chart Evaluation Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationComposition

noncomputable section

/-! Homogeneous-chart evaluation commutes with homomorphisms of its
target ring. This is the naturality needed for ring-valued chart points. -/
universe u v w
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : Type v} [CommRing A] {B : Type w} [CommRing B]

theorem homogeneousAwayEvaluation_comp (g : ℕ → Submodule R S) [GradedAlgebra g]
    (f : S) (φ : S →+* A) (hf : IsUnit (φ f)) (ψ : A →+* B) :
    ψ.comp (AwayEvaluation.homogeneousAwayEvaluation g f φ hf) =
      AwayEvaluation.homogeneousAwayEvaluation g f (ψ.comp φ) (hf.map ψ) := by
  have h : ψ.comp (IsLocalization.Away.lift f hf : Localization.Away f →+* A) =
      (IsLocalization.Away.lift f (g := ψ.comp φ) (hf.map ψ) : Localization.Away f →+* B) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  unfold AwayEvaluation.homogeneousAwayEvaluation
  rw [← RingHom.comp_assoc, h]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEvaluationComposition
