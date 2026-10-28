import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FactorRatios

/-! # Ratio Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RatioEquations

noncomputable section

/-! The coordinate-ratio fraction is uniquely characterized by multiplication by its invertible denominator coordinate. -/

open _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem homogeneousFactorRatio_mul (g : A) (d : ℕ) (hg : g ∈ 𝒜 d)
    (a b c : A) (hac : a * c ∈ 𝒜 d) (h : g = b * c) :
    algebraMap A (Localization.Away g) b * (FactorRatios.homogeneousFactorRatio 𝒜 g d hg a c hac).val =
      algebraMap A (Localization.Away g) a := by
  rw [FactorRatios.homogeneousFactorRatio_val, ← mul_assoc, ← map_mul]
  have he : b * (a * c) = a * g := by rw [h]; ring
  rw [he, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

theorem homogeneousFactorRatio_unique (g : A) (d : ℕ) (hg : g ∈ 𝒜 d)
    (a b c : A) (hac : a * c ∈ 𝒜 d) (h : g = b * c) (x : Localization.Away g)
    (hx : algebraMap A (Localization.Away g) b * x = algebraMap A (Localization.Away g) a) :
    x = (FactorRatios.homogeneousFactorRatio 𝒜 g d hg a c hac).val := by
  have hb : IsUnit (algebraMap A (Localization.Away g) b) :=
    IsLocalization.Away.isUnit_of_dvd (x := g) ⟨c, h⟩
  exact hb.mul_left_cancel (hx.trans (homogeneousFactorRatio_mul 𝒜 g d hg a b c hac h).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RatioEquations
