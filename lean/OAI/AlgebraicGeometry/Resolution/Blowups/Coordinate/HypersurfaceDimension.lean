import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Hypersurface Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.HypersurfaceDimension.Construction

noncomputable section

/-! Smoothness and dimension descent for the actual coordinate hypersurface quotient. -/

section

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Algebra ℚ A] [IsNoetherianRing A]

theorem coordinateHypersurface_dimension_drop (D : Derivation k A A) (z : A) (hz : D z = 1) :
    ringKrullDim (A ⧸ Ideal.span {z}) + 1 ≤ ringKrullDim A :=
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor (Regularity.Construction.coordinate_isRegular D z hz).mem_nonZeroDivisors

/-- The actual coordinate quotient has an ambient dimension bound one lower. -/
theorem coordinateHypersurface_dimension_induction (D : Derivation k A A) (z : A) (hz : D z = 1)
    (d : ℕ) (hd : ringKrullDim A ≤ (d + 1 : ℕ)) : ringKrullDim (A ⧸ Ideal.span {z}) ≤ d := by
  have h := (coordinateHypersurface_dimension_drop D z hz).trans hd
  rw [Nat.cast_add, Nat.cast_one] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

end

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

/-- Every coordinate hypersurface in an étale chart is smooth over the
original coefficient field, with its actual quotient algebra structure. -/
theorem etale_coordinate_hypersurface_smooth (h : σ) :
    Algebra.Smooth K (S ⧸ Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) := by
  let : Algebra.Smooth K (MvPolynomial σ K ⧸ Ideal.span {(MvPolynomial.X h : MvPolynomial σ K)}) :=
    Blowups.Smooth.TransformedCoordinateHypersurface.Construction.coordinateHyperplane_smooth h
  have hs := Blowups.Smooth.TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient (k := K) (A := MvPolynomial σ K) (B := S)
    (Ideal.span {(MvPolynomial.X h : MvPolynomial σ K)})
  rw [Ideal.map_span, Set.image_singleton] at hs
  exact hs

variable [CharZero K] [DecidableEq σ]

omit [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S] in
/-- This coordinate hypersurface is an actual lower-dimensional ambient
space for the coefficient-ideal induction. -/
theorem etale_coordinate_hypersurface_dimension_induction (h : σ) (d : ℕ)
    (hd : ringKrullDim S ≤ (d + 1 : ℕ)) :
    ringKrullDim (S ⧸ Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) ≤ d := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  apply coordinateHypersurface_dimension_induction (Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h)
    (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) _ d hd
  rw [Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X, ite_eq_left rfl]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.HypersurfaceDimension.Construction
