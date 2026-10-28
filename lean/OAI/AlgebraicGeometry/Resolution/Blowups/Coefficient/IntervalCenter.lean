import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval

/-! # Interval Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalCenter.Construction

noncomputable section

/-! Every retained coefficient ideal has the same permissible smooth coordinate centers. -/

universe u

variable {σ L R k : Type u} [Field L] [IsAlgClosed L] [CharZero L]
  [CommRing R] [CommRing k] [Algebra k R]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ L) R] [Algebra.Etale (MvPolynomial σ L) R]
variable {ι : Type*}

/-- Resolving any ideal retained between the normal-family and intrinsic
coefficient bounds chooses exactly the permissible ambient coordinate centers. -/
theorem relative_coefficient_family_interval_center
    (S : Finset σ) (h : σ) (hh : h ∈ S) (D : Derivation k R R)
    (hD : D (algebraMap (MvPolynomial σ L) R (MvPolynomial.X h)) = 1)
    (p : ι → R) (b : ℕ)
    (C : Ideal (R ⧸ Ideal.span {algebraMap (MvPolynomial σ L) R (MvPolynomial.X h)}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D
      (algebraMap (MvPolynomial σ L) R (MvPolynomial.X h)) p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k
      (algebraMap (MvPolynomial σ L) R (MvPolynomial.X h)) (Ideal.span (Set.range p)) b) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal S).map (algebraMap (MvPolynomial σ L) R)
    Ideal.span (Set.range p) ≤ I ^ b ↔
      C ≤ I.map (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial σ L) R (MvPolynomial.X h)})) ^ b.factorial := by
  dsimp only
  constructor
  · intro hJ
    exact hupp.trans (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order k _ _ _ b hJ)
  · intro hC
    exact (WeightedFamilyCenterLift.Construction.etale_coordinate_center_iff_weighted_family_center S h hh D hD p b).mpr (hlow.trans hC)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalCenter.Construction
