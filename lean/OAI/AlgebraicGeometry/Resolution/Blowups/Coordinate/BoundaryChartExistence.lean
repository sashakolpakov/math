import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupBoundaryModel

/-! # Boundary Chart Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryChartExistence.Construction

noncomputable section

/-! Local normal-crossing boundary charts at every prime of any coordinate-center blowup chart. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Fintype σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

/-- The explicit normal-crossing models cover every prime of every
denominator chart, including denominators outside the coordinate family. -/
theorem exists_coordinate_boundary_blowup_open_chart (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ C)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) a)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (BlowupBoundaryModel.Construction.coordinateBoundaryBlowupFamily C a e) p) := by
  obtain ⟨i, q, hq⟩ := Blowup.ChartOverlapCover.Construction.blowupChartOverlap_family_covers
    (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C)
    (Blowups.Etale.MonomialFrame.Construction.etale_subset_coordinate_frame_span C) a p
  exact ⟨{ carrier := .of (BlowupOverlap.Construction.coordinateBlowupOverlap C a i)
           algebra := Blowup.Overlap.Construction.blowupOverlapBaseAlgebra _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) k
           map := Blowup.Overlap.Construction.blowupChartOverlapLeftAlgHom _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) k
           isOpenImmersion := Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_isOpenImmersion _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
           point := q
           point_over := hq
           model := BlowupBoundaryModel.Construction.coordinateBlowupBoundaryModel C a e i }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryChartExistence.Construction
