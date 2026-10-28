import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBaseChange

/-! # Coefficient Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientBaseChange.Construction

noncomputable section

/-! Exact compatibility of intrinsic relative coefficient ideals on étale overlaps. -/

section

variable {R T : Type*} [CommRing R] [CommRing T]

/-- The actual map between a hypersurface quotient and the quotient
by its image equation. -/
def mappedHypersurfaceQuotientMap (φ : R →+* T) (z : R) :
    (R ⧸ Ideal.span {z}) →+* (T ⧸ Ideal.span {φ z}) :=
  Ideal.quotientMap (Ideal.span {φ z}) φ
    ((Ideal.span_singleton_le_iff_mem ((Ideal.span {φ z}).comap φ)).mpr
      (Ideal.mem_span_singleton_self (φ z)))

theorem mappedHypersurfaceQuotientMap_mk (φ : R →+* T) (z p : R) :
    mappedHypersurfaceQuotientMap φ z (Ideal.Quotient.mk (Ideal.span {z}) p) =
      Ideal.Quotient.mk (Ideal.span {φ z}) (φ p) := rfl

end

variable {σ K S T : Type*} [Field K] [CommRing S] [CommRing T] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]
  [Algebra S T] [Algebra.FormallyEtale S T]
  [Algebra (MvPolynomial σ K) T] [Algebra.Etale (MvPolynomial σ K) T]
  [Algebra K T] [IsScalarTower K S T] [IsScalarTower K (MvPolynomial σ K) T]
  [IsScalarTower (MvPolynomial σ K) S T]

include σ in
/-- The intrinsic coefficient ideal agrees exactly on the actual
hypersurface quotient after an étale refinement. This is equality of
ideals, with no chosen transverse derivation in the statement. -/
theorem etale_relativeCoefficientIdeal_baseChange (z : S) (J : Ideal S) (b : ℕ) :
    (CoefficientIdeal.Construction.relativeCoefficientIdeal K z J b).map (mappedHypersurfaceQuotientMap (algebraMap S T) z) =
      CoefficientIdeal.Construction.relativeCoefficientIdeal K (algebraMap S T z) (J.map (algebraMap S T)) b := by
  unfold CoefficientIdeal.Construction.relativeCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply congrArg (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b)
  funext j
  rw [Ideal.map_map]
  change (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K J j.val).map
      ((Ideal.Quotient.mk (Ideal.span {algebraMap S T z})).comp (algebraMap S T)) = _
  rw [← Ideal.map_map, DifferentialBaseChange.Construction.etale_iteratedRelativeDifferentialIdeal_baseChange (σ := σ)]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientBaseChange.Construction
