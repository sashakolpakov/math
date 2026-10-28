import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.WeightedHypersurfaceOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientTransform

/-! # Weighted Coefficient Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientCenterLift.Construction

noncomputable section

/-! Permissible hypersurface coefficient centers lift to actual permissible ambient centers. -/

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- For every selected coordinate center containing the coordinate hypersurface
equation, permissibility of the single weighted coefficient ideal on the
hypersurface is exactly permissibility of the original ambient ideal. -/
theorem etale_coordinate_center_iff_weighted_coefficient_center
    (C : Finset σ) (h : σ) (hh : h ∈ C) (J : Ideal S) (b : ℕ) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
    let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
    J ≤ I ^ b ↔
      ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal (Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h) z J b ≤
        I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
  let D := Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) (S := S) h
  have hzI : z ∈ I := Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨h, hh, rfl⟩)
  have hDz : D z = 1 := by
    have hd := Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X (K := K) (S := S) h h
    rw [ite_eq_left rfl] at hd
    exact hd
  change J ≤ I ^ b ↔ ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z J b ≤
    I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial
  constructor
  · intro hJ
    have hcoeff := (DifferentialCoefficientOrder.Construction.ideal_order_iff_differentialCoefficientIdeals D z hDz J I hzI b).mp hJ
    exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow _ b _ (fun j => hcoeff j.val j.isLt)
  · intro hcoeff
    cases b with
    | zero => simp only [pow_zero, Ideal.one_eq_top, le_top]
    | succ b =>
      apply (Coordinate.CenterPermissibility.Construction.etale_coordinate_center_permissible_iff_closedPoint_order C J b).mpr
      intro q _ hIq
      apply (Blowups.Etale.WeightedHypersurfaceOrder.Construction.etale_coordinate_local_order_iff_weighted_coefficients h J q (hIq hzI) (b + 1)).mpr
      exact hcoeff.trans (pow_le_pow_left' (Ideal.map_mono hIq) (b + 1).factorial)

/-- A center selected by the lower-dimensional weighted coefficient problem
therefore supplies the divisibility condition for the actual ambient blowup. -/
theorem etale_weighted_coefficient_center_gives_blowup_factorization
    (C : Finset σ) (h : σ) (hh : h ∈ C) (J : Ideal S) (b : ℕ) (i : C)
    (hcoeff : ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal
        (Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h)
        (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) J b ≤
      ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)})) ^
          b.factorial) :
    let I := Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C
    let a := Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) C i
    Ideal.span {(Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b} * ControlledTransform.Construction.blowupControlledTransform I J b a =
      J.map (Blowup.Charts.Construction.blowupChartConstants I a) := by
  apply ControlledTransform.Construction.blowup_controlledTransform_factorization
  exact (etale_coordinate_center_iff_weighted_coefficient_center C h hh J b).mpr hcoeff

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientCenterLift.Construction
