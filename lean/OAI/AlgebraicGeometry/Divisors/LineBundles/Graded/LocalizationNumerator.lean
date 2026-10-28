import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.Localization.Basic

/-! # Localization Numerator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator.BundleCycles

noncomputable section

/-! Homogeneous elements in a localization by degree-zero elements have
homogeneous numerators of the same degree, via the actual decomposition maps. -/

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (D : Submonoid A)
    (hD : ∀ d : D, d.val ∈ 𝒜 0)
    (hlocal : letI := f.toRingHom.toAlgebra; IsLocalization D B)

include hD hlocal in
theorem gradedLocalization_homogeneousNumerator (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ ∃ d : D, b * f d.val = f a := by
  let := f.toRingHom.toAlgebra
  let := hlocal
  obtain ⟨⟨a, d⟩, ha⟩ := IsLocalization.surj D b
  change b * f d.val = f a at ha
  refine ⟨(DirectSum.decompose 𝒜 a n).val, (DirectSum.decompose 𝒜 a n).property, d, ?_⟩
  have hm : b * f d.val ∈ ℬ n := by
    exact (show b * f d.val ∈ ℬ (n + 0) from SetLike.mul_mem_graded hb (f.map_mem (hD d)))
  have hp := congrArg (fun x : B => ((DirectSum.decompose ℬ x n).val : B)) ha
  rw [← GradedRingHom.map_directSumDecompose] at hp
  have hsame : (DirectSum.decompose ℬ (b * f d.val) n).val = b * f d.val :=
    DirectSum.decompose_of_mem_same ℬ hm
  exact hsame.symm.trans hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.LocalizationNumerator.BundleCycles
