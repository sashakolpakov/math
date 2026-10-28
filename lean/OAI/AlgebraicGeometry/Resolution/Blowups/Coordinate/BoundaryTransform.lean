import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.TransformedHypersurfaceCoordinates

/-! # Boundary Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform.Construction

noncomputable section

/-! Actual transforms of coordinate boundary components and smoothness of their intersections. -/

section

variable {R : Type*} [CommRing R]

/-- The divided ideal of a boundary equation contained in the center is
the principal ideal of its actual Rees ratio. -/
theorem blowup_principal_coordinate_controlledTransform (I : Ideal R) (a z : I) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {z.val}) 1 a = Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z} := by
  rw [ControlledTransform.Construction.blowupControlledTransform, Ideal.map_span, Set.image_singleton,
    pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val), ← ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z,
    ← Ideal.span_singleton_mul_span_singleton]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)

end

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S]

/-- A boundary component contained in the center and distinct from the
denominator remains the corresponding coordinate boundary after blowup. -/
theorem etale_boundary_component_transform (C : Finset σ) (i h : C) (hhi : h.val ≠ i.val) :
    ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
      (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h.val)}) 1
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) =
      Ideal.span {Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i (MvPolynomial.X h.val)} := by
  rw [blowup_principal_coordinate_controlledTransform _ _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C h),
    TransformedHypersurfaceCoordinates.Construction.etaleSubsetCoordinateMap_center C i h hhi]

omit [DecidableEq σ] in
/-- The old denominator boundary has empty divided transform in this chart;
the new exceptional component is separately the denominator coordinate. -/
theorem etale_denominator_boundary_transform (C : Finset σ) (i : C) :
    ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
      (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X i.val)}) 1
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) = ⊤ := by
  rw [blowup_principal_coordinate_controlledTransform _ _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i),
    Blowups.Etale.CoefficientStep.Construction.blowupChartRatio_self, Ideal.span_singleton_one]

/-- A boundary coordinate outside the center retains its original equation. -/
theorem etale_outside_boundary_transform (C : Finset σ) (i : C) (h : σ) (hh : h ∉ C) :
    ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C)
      (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) 0
        (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) =
      Ideal.span {Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i (MvPolynomial.X h)} := by
  rw [ResidualCoefficientTransform.Construction.blowupControlledTransform_zero, Ideal.map_span, Set.image_singleton,
    Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap, RingHom.comp_apply, SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_outside C i h hh,
    ChartLift.Construction.blowupChartMap_constants]

variable [Finite σ] [Algebra.Etale (MvPolynomial σ K) S]

/-- Every intersection of new coordinate boundary components is smooth.
Together with the component formulas, this verifies preservation of the
coordinate normal-crossing arrangement on every actual chart. -/
theorem etale_blowup_boundary_intersections_smooth (C : Finset σ) (i : C) (B : Finset σ) :
    letI : Algebra K (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i) :=
      Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateBaseAlgebra C i
    Algebra.Smooth K (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i ⧸
      (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal B).map (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := K) (S := S) C i)) := by
  let T := Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateChart (R := K) (S := S) C i
  let : Algebra K T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateBaseAlgebra C i
  let : Algebra (MvPolynomial σ K) T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinatePolynomialAlgebra C i
  let : IsScalarTower K (MvPolynomial σ K) T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateChart_scalarTower C i
  let : Algebra.Etale (MvPolynomial σ K) T := Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateChart_etale C i
  exact Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateCenter_smooth (R := K) (S := T) B

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform.Construction
