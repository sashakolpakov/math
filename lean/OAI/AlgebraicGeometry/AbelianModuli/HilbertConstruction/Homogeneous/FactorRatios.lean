import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.HomogeneousChartFractions
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Factor Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FactorRatios

noncomputable section

/-! Homogeneous fractions describing ratios of coordinates on opens where a product of coordinates is inverted. -/

open _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def homogeneousFactorRatio (g : A) (d : ℕ) (hg : g ∈ 𝒜 d) (a c : A) (hac : a * c ∈ 𝒜 d) :
    HomogeneousLocalization.Away 𝒜 g :=
  HomogeneousLocalization.Away.mk 𝒜 hg 1 (a * c) (by simpa only [one_smul] using hac)

theorem homogeneousFactorRatio_val (g : A) (d : ℕ) (hg : g ∈ 𝒜 d) (a c : A) (hac : a * c ∈ 𝒜 d) :
    (homogeneousFactorRatio 𝒜 g d hg a c hac).val =
      algebraMap A (Localization.Away g) (a * c) * IsLocalization.Away.invSelf g := by
  change Localization.mk (a * c) ⟨g ^ 1, by use 1⟩ = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change algebraMap A (Localization.Away g) (a * c) =
    (algebraMap A (Localization.Away g) (a * c) * IsLocalization.Away.invSelf g) *
      algebraMap A (Localization.Away g) (g ^ 1)
  rw [pow_one, mul_assoc, mul_comm (IsLocalization.Away.invSelf g),
    IsLocalization.Away.mul_invSelf, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FactorRatios
