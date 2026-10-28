import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Homogeneous Division -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.HomogeneousDivision.BundleCycles

noncomputable section

/-! A homogeneous multiple of a homogeneous element has a quotient
of the expected degree, obtained from the genuine graded decomposition. -/

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem graded_homogeneous_division {t a : A} {i n : ℕ} (ht : t ∈ 𝒜 i)
    (ha : a ∈ 𝒜 (i + n)) (hdiv : t ∣ a) : ∃ b : A, b ∈ 𝒜 n ∧ a = t * b := by
  obtain ⟨b, rfl⟩ := hdiv
  refine ⟨(DirectSum.decompose 𝒜 b n).val, (DirectSum.decompose 𝒜 b n).property, ?_⟩
  exact (DirectSum.decompose_of_mem_same 𝒜 ha).symm.trans
    (DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ht)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.HomogeneousDivision.BundleCycles
