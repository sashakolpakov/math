import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.AwayEvaluation

/-! # Chart Endomorphism Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEndomorphismIdentity

noncomputable section

/-! Cross multiplication in the ambient localization detects the identity
endomorphism of a homogeneous chart. Both denominators are units, and the
ambient chart embedding is injective over arbitrary coefficient rings. -/
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (S : Subalgebra R A) (g : ℕ → Submodule R S) [GradedAlgebra g]
variable (f : S) {d : ℕ} (hfd : f ∈ g d)
variable (φ : S →+* HomogeneousLocalization.Away g f) (hφ : IsUnit (φ f))

include hfd in
theorem homogeneousChartEndomorphism_eq_id
    (hcross : ∀ (k : ℕ) (p : S), p ∈ g (k • d) →
      SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f (φ p) *
          (algebraMap A (Localization.Away f.val) f.val) ^ k =
        SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f (φ f) ^ k *
          algebraMap A (Localization.Away f.val) p.val) :
    AwayEvaluation.homogeneousAwayEvaluation g f φ hφ = RingHom.id (HomogeneousLocalization.Away g f) := by
  let E := SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f
  let F := AwayEvaluation.homogeneousAwayEvaluation g f φ hφ
  apply RingHom.ext
  intro x
  obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective g hfd x
  let x := HomogeneousLocalization.Away.mk g hfd k p hp
  have he : E (F x) * E (φ f) ^ k = E (φ p) := by
    simpa only [map_mul, map_pow] using congrArg E
      (AwayEvaluation.homogeneousAwayEvaluation_mk_cross g f φ hφ hfd k p hp)
  have ho : E x * (algebraMap A (Localization.Away f.val) f.val) ^ k =
      algebraMap A (Localization.Away f.val) p.val := by
    rw [show E x = IsLocalization.mk' (M := Submonoid.powers f.val) (Localization.Away f.val) p.val
      ⟨f.val ^ k, ⟨k, rfl⟩⟩ from SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_mk S g f hfd k p hp,
      ← map_pow]
    exact IsLocalization.mk'_spec (Localization.Away f.val) p.val
      (⟨f.val ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f.val)
  apply SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_injective S g f
  change E (F x) = E x
  apply (((hφ.map E).pow k).mul
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f.val) f.val).pow k)).mul_right_cancel
  calc
    E (F x) * (E (φ f) ^ k * (algebraMap A (Localization.Away f.val) f.val) ^ k) =
        (E (F x) * E (φ f) ^ k) * (algebraMap A (Localization.Away f.val) f.val) ^ k :=
      (mul_assoc _ _ _).symm
    _ = E (φ p) * (algebraMap A (Localization.Away f.val) f.val) ^ k := by rw [he]
    _ = E (φ f) ^ k * algebraMap A (Localization.Away f.val) p.val := hcross k p hp
    _ = E (φ f) ^ k * (E x * (algebraMap A (Localization.Away f.val) f.val) ^ k) := by rw [ho]
    _ = E x * (E (φ f) ^ k * (algebraMap A (Localization.Away f.val) f.val) ^ k) := by ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEndomorphismIdentity
