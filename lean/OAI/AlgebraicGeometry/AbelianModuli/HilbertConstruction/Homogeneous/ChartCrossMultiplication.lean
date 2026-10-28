import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding

/-! # Chart Cross Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartCrossMultiplication

noncomputable section

/-! A polynomial cross-multiplication identity becomes an exact
identity in the ambient localization of a homogeneous Proj chart. -/
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (S : Subalgebra R A) (g : ℕ → Submodule R S) [GradedAlgebra g] (f : S)

theorem homogeneousSubalgebraChartEmbedding_crossMultiply {d : ℕ}
    (hf : f ∈ g d) (x : S) (hx : x ∈ g d) (b c : A) (h : x.val * b = f.val * c) :
    SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f
        (HomogeneousLocalization.Away.mk g hf 1 x (by simpa only [one_nsmul] using hx)) *
        algebraMap A (Localization.Away f.val) b =
      algebraMap A (Localization.Away f.val) c := by
  rw [SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding_mk]
  simp only [pow_one]
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm b, h]
  exact IsLocalization.mk'_mul_cancel_left c (⟨f.val, ⟨1, pow_one _⟩⟩ : Submonoid.powers f.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartCrossMultiplication
