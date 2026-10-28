import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupOverlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupCoordinateLabels

/-! # Blowup Boundary Model -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupBoundaryModel.Construction

noncomputable section

/-! Actual local normal-crossing models including the new exceptional equation. -/

universe u v

variable {σ k S : Type u} {ι : Type v} [DecidableEq σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S]

/-- The new exceptional equation and each individually retained old
divided equation, on the original arbitrary denominator chart. -/
def coordinateBoundaryBlowupFamily (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ C) :
    Option ι → Blowup.Charts.Construction.blowupChart (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) a
  | none => Blowup.Charts.Construction.blowupChartConstants _ a a.val
  | some j => ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C (e j))

variable [Fintype σ] [Algebra.Etale (MvPolynomial σ k) S]
  [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

/-- On the genuine overlap with coordinate chart `i`, all old boundary
equations and the new exceptional equation have an explicit étale
normal-crossing model over the original field. -/
def coordinateBlowupBoundaryModel (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (e : ι ↪ C) (i : C) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (BlowupOverlap.Construction.coordinateBlowupOverlap C a i) (Option ι)
      (fun j => Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
        (coordinateBoundaryBlowupFamily C a e j)) := by
  let e' : ι ↪ σ := ⟨fun j => (e j).val, fun _ _ h => e.injective (Subtype.ext h)⟩
  let u := Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    (ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i))
  let v := Blowup.ChartOverlap.Construction.blowupChartOverlapRight _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    (ExceptionalIdeal.Construction.blowupChartRatio _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) a)
  refine { indices := σ
           finite := inferInstance
           decidableEq := inferInstance
           map := BlowupOverlap.Construction.coordinateBlowupOverlapMap C a i
           etale := BlowupOverlap.Construction.coordinateBlowupOverlapMap_etale C a i
           ground := BlowupOverlap.Construction.coordinateBlowupOverlapMap_ground C a i
           coordinate := Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate e' i.val
           distinct := Boundary.BlowupCoordinateLabels.Construction.blownBoundaryCoordinate_distinct e' i.val
           multiplier := fun j => match j with | none => v | some _ => u
           multiplierUnit := ?_
           equation := ?_ }
  · intro j
    cases j with
    | none => exact Blowup.OverlapTransitions.Construction.blowupChartOverlapRight_ratio_isUnit _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
    | some j => exact Blowup.OverlapTransitions.Construction.blowupChartOverlapLeft_ratio_isUnit _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
  · intro j
    cases j with
    | none => exact BlowupOverlap.Construction.coordinateBlowupOverlap_exceptional C a i
    | some j =>
        change Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
          (ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C (e j))) =
            u * match (if (e j).val = i.val then none else some (e j).val) with
                | none => 1
                | some s => BlowupOverlap.Construction.coordinateBlowupOverlapMap C a i (MvPolynomial.X s)
        split_ifs with h
        · simpa only [ite_eq_left h] using BlowupOverlap.Construction.coordinateBlowupOverlap_boundary C a i (e j)
        · simpa only [ite_eq_right h] using BlowupOverlap.Construction.coordinateBlowupOverlap_boundary C a i (e j)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupBoundaryModel.Construction
