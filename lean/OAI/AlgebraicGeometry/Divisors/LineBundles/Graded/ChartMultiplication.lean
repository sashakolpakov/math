import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition

/-! # Chart Multiplication -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication.BundleCycles

noncomputable section

/-! Multiplication and normalization of genuine homogeneous affine-chart fractions. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedAway_mk_mul {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n m : ℕ)
    (a b : A) (ha : a ∈ 𝒜 (n • k)) (hb : b ∈ 𝒜 (m • k)) :
    Away.mk 𝒜 hs n a ha * Away.mk 𝒜 hs m b hb =
      Away.mk 𝒜 hs (n + m) (a * b) (by rw [add_smul]; exact SetLike.mul_mem_graded ha hb) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  exact congrArg (Localization.mk (a * b)) (Subtype.ext (pow_add s n m).symm)

theorem gradedAway_mk_self {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    Away.mk 𝒜 hs 1 s (by simpa only [one_smul] using hs) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_one]
  have he : (⟨s ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers s) = ⟨s, Submonoid.mem_powers s⟩ :=
    Subtype.ext (pow_one s)
  exact (congrArg (Localization.mk s) he).trans
    (Localization.mk_self (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication.BundleCycles
