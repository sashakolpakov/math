import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Zero Units -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits.BundleCycles

noncomputable section

/-! A unit of degree zero is already a unit in the actual degree-zero ring. -/

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedZero_isUnit (a : 𝒜 0) (ha : IsUnit a.val) : IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  have hmul : a.val * (↑u⁻¹ : A) = 1 := by rw [← hu]; exact u.val_inv
  let b : 𝒜 0 := DirectSum.decompose 𝒜 (↑u⁻¹ : A) 0
  have hproj := congrArg (fun z : A => ((DirectSum.decompose 𝒜 z 0).val : A)) hmul
  have he : a.val * b.val = 1 := by
    rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 a.property,
      DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜)] at hproj
    exact hproj
  exact IsUnit.of_mul_eq_one b (Subtype.ext he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ZeroUnits.BundleCycles
