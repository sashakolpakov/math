import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.HypersurfaceDimension

/-! # Retraction Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionDimension.Construction

noncomputable section

/-! The hypersurface retained by the retraction is smooth and has the required lower dimension. -/

universe u

variable {σ k R : Type u} [Field k] [CommRing R] [Finite σ]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]

theorem coordinateLineFiber_smooth (h : σ) : Algebra.Smooth k (MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h) := by
  let : Algebra.Smooth k (R ⧸ Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)}) :=
    HypersurfaceDimension.Construction.etale_coordinate_hypersurface_smooth h
  exact Algebra.Smooth.of_equiv (MvPolynomialRetraction.Construction.coordinateLineFiberEquiv (k := k) (R := R) h).symm

omit [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R] in
theorem coordinateLineFiber_isNoetherian (h : σ) : IsNoetherianRing (MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ k) R
  infer_instance

omit [IsScalarTower k (MvPolynomial σ k) R] in
/-- The retained coefficient ring is a valid smaller-dimensional ambient
ring for the next stage of the resolution induction. -/
theorem coordinateLineFiber_dimension_induction [CharZero k] [DecidableEq σ]
    (h : σ) (d : ℕ) (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ringKrullDim (MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h) ≤ d := by
  rw [(MvPolynomialRetraction.Construction.coordinateLineFiberEquiv (k := k) (R := R) h).toRingEquiv.ringKrullDim]
  exact HypersurfaceDimension.Construction.etale_coordinate_hypersurface_dimension_induction h d hd

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionDimension.Construction
