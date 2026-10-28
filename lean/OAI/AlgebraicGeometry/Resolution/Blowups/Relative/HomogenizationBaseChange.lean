import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBaseChange

/-! # Homogenization Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationBaseChange.Construction

noncomputable section

/-! The homogenized comparison ideal is intrinsic on étale overlaps. -/

variable {σ K S T : Type*} [Field K] [CommRing S] [CommRing T] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]
  [Algebra S T] [Algebra.FormallyEtale S T]
  [Algebra (MvPolynomial σ K) T] [Algebra.Etale (MvPolynomial σ K) T]
  [Algebra K T] [IsScalarTower K S T] [IsScalarTower K (MvPolynomial σ K) T]
  [IsScalarTower (MvPolynomial σ K) S T]

include σ in
/-- Homogenization commutes exactly with the actual étale refinement. -/
theorem etale_relativeHomogenizedIdeal_baseChange (J : Ideal S) (n : ℕ) :
    (DifferentialEquiv.Construction.relativeHomogenizedIdeal K J n).map (algebraMap S T) =
      DifferentialEquiv.Construction.relativeHomogenizedIdeal K (J.map (algebraMap S T)) n := by
  unfold DifferentialEquiv.Construction.relativeHomogenizedIdeal
  simp only [Ideal.map_iSup, Ideal.map_mul, Ideal.map_pow,
    DifferentialBaseChange.Construction.etale_iteratedRelativeDifferentialIdeal_baseChange (σ := σ)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationBaseChange.Construction
