import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.OverlapOutsideBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupBoundaryModel

/-! # Coordinate Boundary Family -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryFamily.Construction

noncomputable section

/-! Actual divided and unchanged boundary equations for a general coordinate-compatible center. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S]

/-- Old equations containing the center are divided once; old equations
transverse to the center are pulled back unchanged. The new exceptional
equation keeps its own label. -/
def mixedCoordinateBoundaryFamily (C : Finset σ)
    (a : Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ σ) :
    Option ι → Blowup.Charts.Construction.blowupChart (Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) a
  | none => Blowup.Charts.Construction.blowupChartConstants _ a a.val
  | some j => if h : e j ∈ C then
      ExceptionalIdeal.Construction.blowupChartRatio _ a (Etale.CoefficientStep.Construction.etaleCoordinateElement C ⟨e j, h⟩)
    else Blowup.Charts.Construction.blowupChartConstants _ a (algebraMap (MvPolynomial σ k) S (MvPolynomial.X (e j)))

/-- Every old equation satisfies its exact control-zero or control-one
factorization on the actual arbitrary-denominator chart. -/
theorem mixedCoordinateBoundaryFamily_factorization (C : Finset σ)
    (a : Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ σ) (j : ι) :
    Blowup.Charts.Construction.blowupChartConstants _ a (algebraMap (MvPolynomial σ k) S (MvPolynomial.X (e j))) =
      (Blowup.Charts.Construction.blowupChartConstants _ a a.val) ^ (if e j ∈ C then 1 else 0) *
        mixedCoordinateBoundaryFamily C a e (some j) := by
  by_cases hj : e j ∈ C
  · rw [mixedCoordinateBoundaryFamily, dite_eq_left hj, ite_eq_left hj,
      pow_one (Blowup.Charts.Construction.blowupChartConstants _ a a.val)]
    exact (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio _ a (Etale.CoefficientStep.Construction.etaleCoordinateElement C ⟨e j, hj⟩)).symm
  · rw [mixedCoordinateBoundaryFamily, dite_eq_right hj, ite_eq_right hj,
      pow_zero (Blowup.Charts.Construction.blowupChartConstants _ a a.val),
      one_mul (Blowup.Charts.Construction.blowupChartConstants _ a (algebraMap (MvPolynomial σ k) S (MvPolynomial.X (e j))))]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryFamily.Construction
