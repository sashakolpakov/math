import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryModel

/-! # Coordinate Boundary Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryCharts.Construction

noncomputable section

/-! Full mixed boundary models at every prime of every coordinate-compatible blowup chart. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Fintype σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

/-- Each arbitrary denominator chart has a genuine open normal-crossing
model through every prime, for both divided and transverse old components
together with the new exceptional equation. -/
theorem exists_mixed_coordinate_boundary_open_chart (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ σ)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) a)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily C a e) p) := by
  obtain ⟨i, q, hq⟩ := Blowup.ChartOverlapCover.Construction.blowupChartOverlap_family_covers
    (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C)
    (Blowups.Etale.MonomialFrame.Construction.etale_subset_coordinate_frame_span C) a p
  exact ⟨{ carrier := .of (Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlap C a i)
           algebra := Blowup.Overlap.Construction.blowupOverlapBaseAlgebra _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) k
           map := Blowup.Overlap.Construction.blowupChartOverlapLeftAlgHom _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) k
           isOpenImmersion := Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_isOpenImmersion _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
           point := q
           point_over := hq
           model := CoordinateBoundaryModel.Construction.mixedCoordinateBoundaryModel C a e i }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryCharts.Construction
