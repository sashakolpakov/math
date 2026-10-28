import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Transverse Direction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirection.Construction

noncomputable section

/-! Transversality is independent of the complementary étale coordinates. -/

variable {σ K S C : Type*} [Field K] [CommRing S] [CommRing C]
  [Algebra K S] [Algebra K C]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [IsScalarTower K (MvPolynomial σ K) S] [Fintype σ] [DecidableEq σ]

/-- A derivation annihilating the boundary equations and detecting the
equation at the point supplies a nonzero coordinate partial outside the boundary. -/
theorem exists_transverse_partial_of_boundary_derivation
    (B : Finset σ) (D : Derivation K S S) (r : S →ₐ[K] C) (z : S)
    (hB : ∀ b ∈ B, D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X b)) = 0)
    (hz : r (D z) ≠ 0) :
    ∃ i : σ, i ∉ B ∧ r (DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) i z) ≠ 0 := by
  by_contra h
  push Not at h
  apply hz
  rw [ModuleDerivations.Construction.etale_relative_derivation_apply (σ := σ) D z, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul]
  by_cases hi : i ∈ B
  · rw [hB i hi, map_zero, zero_mul]
  · rw [h i hi, mul_zero]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirection.Construction
