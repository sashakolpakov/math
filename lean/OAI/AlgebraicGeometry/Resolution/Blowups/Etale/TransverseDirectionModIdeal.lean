import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Transverse Direction Mod Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirectionModIdeal.Construction

noncomputable section

/-! Boundary derivatives need only vanish modulo the comparison prime to detect a transverse direction. -/

theorem exists_transverse_partial_mod_ideal
    {σ k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]
    (B : Finset σ) (D : Derivation k R R) (I : Ideal R) (z : R)
    (hB : ∀ i ∈ B, D (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)) ∈ I)
    (hz : D z ∉ I) : ∃ i : σ, i ∉ B ∧ DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z ∉ I := by
  by_contra h
  push Not at h
  apply hz
  rw [ModuleDerivations.Construction.etale_relative_derivation_apply (σ := σ) D z]
  apply I.sum_mem
  intro i _
  by_cases hi : i ∈ B
  · exact I.mul_mem_right _ (hB i hi)
  · exact I.mul_mem_left _ (h i hi)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirectionModIdeal.Construction
