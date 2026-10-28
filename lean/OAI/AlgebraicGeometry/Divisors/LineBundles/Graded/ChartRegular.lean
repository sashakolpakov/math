import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition
import Mathlib.Algebra.Ring.NonZeroDivisors

/-! # Chart Regular -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartRegular.BundleCycles

noncomputable section

/-! A regular homogeneous numerator gives a regular element of the
actual homogeneous affine-chart ring. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedAway_mk_isRegular {s : A} {k : ℕ} (hs : s ∈ 𝒜 k)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • k)) (hreg : IsRegular a) :
    IsRegular (Away.mk 𝒜 hs n a ha) := by
  have ha' : a ∈ nonZeroDivisors A := isRegular_iff_mem_nonZeroDivisors.mp hreg
  have hloc' : algebraMap A (Localization.Away s) a ∈ nonZeroDivisors (Localization.Away s) :=
    IsLocalization.nonZeroDivisors_le_comap (S := Localization.Away s) (M := Submonoid.powers s) ha'
  have hloc : IsRegular (algebraMap A (Localization.Away s) a) :=
    isRegular_iff_mem_nonZeroDivisors.mpr hloc'
  have hv : IsRegular (Away.mk 𝒜 hs n a ha).val := by
    rw [Away.val_mk, Localization.mk_eq_mk']
    apply IsRegular.of_mul_left (b := algebraMap A (Localization.Away s) (s ^ n))
    rw [IsLocalization.mk'_spec]
    exact hloc
  have hl : IsLeftRegular (Away.mk 𝒜 hs n a ha) := by
    intro x y h
    apply HomogeneousLocalization.val_injective
    apply hv.left
    simpa only [val_mul] using congrArg HomogeneousLocalization.val h
  exact ⟨hl, fun x y h => hl ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartRegular.BundleCycles
