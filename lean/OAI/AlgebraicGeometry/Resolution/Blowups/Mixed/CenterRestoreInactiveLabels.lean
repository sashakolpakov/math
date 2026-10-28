import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterPartialLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryLabelRestriction

/-! # Center Restore Inactive Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restore all inactive original labels while keeping the adjoined normal equation. -/

universe u v

def MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.restoreInactiveWithNormal
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [DecidableEq ι] (B F : Finset ι) (hFB : F ⊆ B)
    {I : Ideal R} (z : R) (w : ι → R) (hu : ∀ j, j ∉ B → IsUnit (w j))
    {p : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I
      (fun j : Option B => match j with | none => z | some j => w j.val)
      (insert none ((ActiveBoundaryLabelRestriction.Construction.restrictedBoundaryDividedLabels B F).image some)) p) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) p := by
  classical
  let r := OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel (ActiveBoundaryLabelRestriction.Construction.boundaryLabelRestriction B)
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  let a : Option ι → R := fun j => match j with | none => 1 | some j => if j ∈ B then 1 else w j
  have ha (j : Option ι) : IsUnit (a j) := by
    cases j with
    | none => exact isUnit_one
    | some j =>
        by_cases hj : j ∈ B
        · simpa only [a, ite_eq_left hj] using (isUnit_one : IsUnit (1 : R))
        · simpa only [a, ite_eq_right hj] using hu j hj
  apply C.pullbackLabels r
    (OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel_distinct _ (ActiveBoundaryLabelRestriction.Construction.boundaryLabelRestriction_distinct B)) v a ha
    (fun j => ?_) (insert none (F.image some)) (ActiveBoundaryLabelRestriction.Construction.active_boundary_adjoined_divided_iff B F hFB)
  cases j with
  | none => exact (one_mul z).symm
  | some j =>
      by_cases hj : j ∈ B
      · simp only [v, a, ite_eq_left hj, r, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, ActiveBoundaryLabelRestriction.Construction.boundaryLabelRestriction,
          dite_eq_left hj, Option.map_some, one_mul]
      · simp only [v, a, ite_eq_right hj, r, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, ActiveBoundaryLabelRestriction.Construction.boundaryLabelRestriction,
          dite_eq_right hj, Option.map_none, mul_one]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
