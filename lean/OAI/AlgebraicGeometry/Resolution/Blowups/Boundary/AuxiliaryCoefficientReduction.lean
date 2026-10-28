import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.HypersurfaceDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.WeightedHypersurfaceOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientCenterLift

/-! # Auxiliary Coefficient Reduction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryCoefficientReduction.Construction

noncomputable section

/-! The actual lower-dimensional coefficient problem for a boundary auxiliary ideal. -/

universe u

variable {σ K S : Type u} [Field K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- The single weighted coefficient ideal of the auxiliary problem on the
actual quotient by the selected old boundary coordinate. -/
def boundaryAuxiliaryCoefficientIdeal (B : Finset σ) (h : σ) (J : Ideal S) (m : ℕ) :
    Ideal (S ⧸ Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) :=
  ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal (Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h)
    (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h))
    (AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)) (m + 1)

variable [CharZero K] [IsAlgClosed K] [Finite σ]

/-- The whole auxiliary high-order locus is detected by the lower-dimensional
coefficient ideal; membership in the chosen hypersurface is derived from the
proved differential membership of its equation. -/
theorem boundaryAuxiliaryCoefficientIdeal_order_locus_iff
    (B : Finset σ) (h : σ) (hhB : h ∈ B) (J q : Ideal S) [q.IsMaximal] (m : ℕ) :
    AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1) ≤ q ^ (m + 1) ↔
      algebraMap (MvPolynomial σ K) S (MvPolynomial.X h) ∈ q ∧
        boundaryAuxiliaryCoefficientIdeal (K := K) B h J m ≤
          q.map (Ideal.Quotient.mk
            (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)})) ^ (m + 1).factorial := by
  let H := AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
  let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
  have hlog := AuxiliaryIdeal.Construction.etale_boundary_auxiliary_logarithmic_equation (K := K) (S := S)
    B ∅ h hhB (Finset.notMem_empty h) J m
  have hzordinary : z ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal H m :=
    (LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal_le_ordinary
      (fun j : (∅ : Finset σ) => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)) H m) hlog.2
  constructor
  · intro hH
    have hzq : z ∈ q := by
      have hdiff := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow q H 1 m
        (by simpa only [Nat.add_comm 1 m] using hH)
      simpa only [pow_one] using hdiff hzordinary
    refine ⟨hzq, ?_⟩
    exact (Blowups.Etale.WeightedHypersurfaceOrder.Construction.etale_coordinate_local_order_iff_weighted_coefficients h H q hzq (m + 1)).mp
      ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff H q (m + 1)).mpr hH)
  · rintro ⟨hzq, hC⟩
    apply (ClosedWeightedOrder.Construction.closedPoint_local_order_iff H q (m + 1)).mp
    exact (Blowups.Etale.WeightedHypersurfaceOrder.Construction.etale_coordinate_local_order_iff_weighted_coefficients h H q hzq (m + 1)).mpr hC

/-- A permissible center for the actual coefficient ideal lifts to a
permissible center for the original ideal lying inside every selected old
boundary component. -/
theorem boundaryAuxiliaryCoefficient_center_lift
    (B C : Finset σ) (h : σ) (hhC : h ∈ C) (J : Ideal S) (m : ℕ)
    (hcoef : boundaryAuxiliaryCoefficientIdeal (K := K) B h J m ≤
      (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C).map
        (Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)})) ^
          (m + 1).factorial) :
    J ≤ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ^ (m + 1) ∧
      Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B ≤ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C := by
  let H := AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
  have hH : H ≤ Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) C ^ (m + 1) :=
    (WeightedCoefficientCenterLift.Construction.etale_coordinate_center_iff_weighted_coefficient_center C h hhC H (m + 1)).mpr hcoef
  exact (AuxiliaryIdeal.Construction.etale_boundary_auxiliary_center_iff C J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B)
    (m + 1) (Nat.zero_lt_succ m)).mp hH

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryCoefficientReduction.Construction
