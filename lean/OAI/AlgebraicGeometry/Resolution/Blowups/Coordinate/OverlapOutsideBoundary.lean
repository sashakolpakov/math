import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupOverlap

/-! # Overlap Outside Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.OverlapOutsideBoundary.Construction

noncomputable section

/-! Boundary coordinates transverse to the center remain unchanged on actual overlaps. -/

universe u

variable {σ k S : Type u} [DecidableEq σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S]

theorem coordinateBlowupOverlap_outside_boundary (C : Finset σ)
    (a : Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) (j : σ) (hj : j ∉ C) :
    Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
        (Blowup.Charts.Construction.blowupChartConstants _ a (algebraMap (MvPolynomial σ k) S (MvPolynomial.X j))) =
      BlowupOverlap.Construction.coordinateBlowupOverlapMap C a i (MvPolynomial.X j) := by
  rw [Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_constants, BlowupOverlap.Construction.coordinateBlowupOverlapMap, RingHom.comp_apply,
    Etale.MonomialStep.Construction.etaleSubsetCoordinateMap, RingHom.comp_apply,
    SubsetCoordinateBlowup.Construction.polynomialToSubsetCoordinateBlowup_outside C i j hj, ChartLift.Construction.blowupChartMap_constants,
    Blowup.ChartOverlap.Construction.blowupChartOverlapRight_constants]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.OverlapOutsideBoundary.Construction
