import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ProjectiveQuotient
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Chart Ratios -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartRatios

noncomputable section

/-!
Degree-one coordinate ratios on the intersection of two projective charts.
These computations identify the two normalizations in a common actual
homogeneous localization, including when the coefficient ring has torsion.
-/

open _root_.HomogeneousLocalization

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem homogeneousFraction_val {d : ℕ} {s : A} (hs : s ∈ 𝒜 d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    (Away.mk 𝒜 hs n a ha).val =
      algebraMap A (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n := by
  erw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  rw [map_pow, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf s),
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]

variable {s t : A} (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1)

def degreeOneFraction (u : 𝒜 1) : Away 𝒜 s :=
  Away.mk 𝒜 hs 1 u.val (by simpa only [one_smul] using u.property)

def overlapRatioLeft (u : 𝒜 1) : Away 𝒜 (s * t) :=
  Away.mk 𝒜 (SetLike.mul_mem_graded hs ht) 1 (u.val * t)
    (by simpa only [one_smul] using SetLike.mul_mem_graded u.property ht)

def overlapRatioRight (u : 𝒜 1) : Away 𝒜 (s * t) :=
  Away.mk 𝒜 (SetLike.mul_mem_graded hs ht) 1 (u.val * s)
    (by simpa only [one_smul] using SetLike.mul_mem_graded u.property hs)

theorem awayMap_degreeOneFraction_left (u : 𝒜 1) :
    awayMap 𝒜 ht rfl (degreeOneFraction 𝒜 hs u) = overlapRatioLeft 𝒜 hs ht u := by
  rw [degreeOneFraction, awayMap_mk]
  simp only [pow_one, overlapRatioLeft]

theorem awayMap_degreeOneFraction_right (u : 𝒜 1) :
    awayMap 𝒜 hs (mul_comm s t) (degreeOneFraction 𝒜 ht u) = overlapRatioRight 𝒜 hs ht u := by
  rw [degreeOneFraction, awayMap_mk]
  simp only [pow_one, overlapRatioRight]

theorem overlapRatioLeft_val (u : 𝒜 1) :
    (overlapRatioLeft 𝒜 hs ht u).val =
      algebraMap A (Localization.Away (s * t)) u.val *
        algebraMap A (Localization.Away (s * t)) t * IsLocalization.Away.invSelf (s * t) := by
  rw [overlapRatioLeft, homogeneousFraction_val, pow_one, map_mul]

theorem overlapRatioRight_val (u : 𝒜 1) :
    (overlapRatioRight 𝒜 hs ht u).val =
      algebraMap A (Localization.Away (s * t)) u.val *
        algebraMap A (Localization.Away (s * t)) s * IsLocalization.Away.invSelf (s * t) := by
  rw [overlapRatioRight, homogeneousFraction_val, pow_one, map_mul]

theorem overlapRatio_pivots_mul :
    overlapRatioLeft 𝒜 hs ht ⟨t, ht⟩ * overlapRatioRight 𝒜 hs ht ⟨s, hs⟩ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_one, overlapRatioLeft_val, overlapRatioRight_val]
  let φ := algebraMap A (Localization.Away (s * t))
  let v : Localization.Away (s * t) := IsLocalization.Away.invSelf (s * t)
  have hv : φ s * φ t * v = 1 := by
    rw [← map_mul]
    exact IsLocalization.Away.mul_invSelf (s * t)
  change (φ t * φ t * v) * (φ s * φ s * v) = 1
  calc
    _ = (φ s * φ t * v) ^ 2 := by ring
    _ = 1 := by rw [hv, one_pow]

theorem overlapRatio_pivot_isUnit : IsUnit (overlapRatioLeft 𝒜 hs ht ⟨t, ht⟩) :=
  isUnit_iff_exists_inv.mpr ⟨overlapRatioRight 𝒜 hs ht ⟨s, hs⟩, overlapRatio_pivots_mul 𝒜 hs ht⟩

theorem overlapRatio_cross (u : 𝒜 1) :
    overlapRatioLeft 𝒜 hs ht ⟨t, ht⟩ * overlapRatioRight 𝒜 hs ht u = overlapRatioLeft 𝒜 hs ht u := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, overlapRatioLeft_val, overlapRatioRight_val, overlapRatioLeft_val]
  let φ := algebraMap A (Localization.Away (s * t))
  let v : Localization.Away (s * t) := IsLocalization.Away.invSelf (s * t)
  have hv : φ s * φ t * v = 1 := by
    rw [← map_mul]
    exact IsLocalization.Away.mul_invSelf (s * t)
  change (φ t * φ t * v) * (φ u.val * φ s * v) = φ u.val * φ t * v
  calc
    _ = (φ s * φ t * v) * (φ u.val * φ t * v) := by ring
    _ = _ := by rw [hv, one_mul]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartRatios
