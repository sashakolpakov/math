import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension

/-! # Normal Quotient Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDimension.Construction

noncomputable section

/-! Dimension drop for any actual normal equation with a unit derivative. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]

theorem normal_quotient_dimension_induction (D : Derivation k R R) (z : R) (hz : D z = 1)
    (d : ℕ) (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (R ⧸ Ideal.span {z}) ≤ d := by
  have h := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor (Coordinate.Regularity.Construction.coordinate_isRegular D z hz).mem_nonZeroDivisors).trans hd
  rw [Nat.cast_add, Nat.cast_one] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDimension.Construction
