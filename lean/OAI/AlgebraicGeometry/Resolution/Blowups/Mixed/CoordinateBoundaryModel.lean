import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryFamily

/-! # Coordinate Boundary Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryModel.Construction

noncomputable section

/-! Full coordinate boundary models for a center meeting some old components transversely. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Fintype σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

/-- A coordinate-compatible center preserves the whole coordinate
boundary, including components outside the center coordinate set, on
the actual common open chart of any original denominator. -/
def mixedCoordinateBoundaryModel (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ σ) (i : C) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlap C a i) (Option ι)
      (fun j => Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
        (CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily C a e j)) := by
  let u := Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    (ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i))
  let v := Blowup.ChartOverlap.Construction.blowupChartOverlapRight _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    (ExceptionalIdeal.Construction.blowupChartRatio _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) a)
  refine { indices := σ
           finite := inferInstance
           decidableEq := inferInstance
           map := Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlapMap C a i
           etale := Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlapMap_etale C a i
           ground := Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlapMap_ground C a i
           coordinate := Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate e i.val
           distinct := Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate_distinct e i.val
           multiplier := fun j => match j with | none => v | some l => if e l ∈ C then u else 1
           multiplierUnit := ?_
           equation := ?_ }
  · intro j
    cases j with
    | none => exact Blowup.OverlapTransitions.Construction.blowupChartOverlapRight_ratio_isUnit _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    | some j =>
        by_cases hj : e j ∈ C
        · simpa only [ite_eq_left hj] using Blowup.OverlapTransitions.Construction.blowupChartOverlapLeft_ratio_isUnit _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
        · simp only [ite_eq_right hj, isUnit_one]
  · intro j
    cases j with
    | none => exact Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlap_exceptional C a i
    | some j =>
        by_cases hj : e j ∈ C
        · simp only [CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily, dite_eq_left hj, ite_eq_left hj, Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate]
          by_cases hji : e j = i.val
          · simpa only [ite_eq_left hji] using
              Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlap_boundary C a i ⟨e j, hj⟩
          · simpa only [ite_eq_right hji] using
              Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlap_boundary C a i ⟨e j, hj⟩
        · have hji : e j ≠ i.val := fun h => hj (h ▸ i.property)
          simp only [CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily, dite_eq_right hj, ite_eq_right hj,
            Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate, ite_eq_right hji]
          rw [one_mul (Coordinate.BlowupOverlap.Construction.coordinateBlowupOverlapMap C a i (MvPolynomial.X (e j)))]
          exact Coordinate.OverlapOutsideBoundary.Construction.coordinateBlowupOverlap_outside_boundary C a i (e j) hj

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CoordinateBoundaryModel.Construction
