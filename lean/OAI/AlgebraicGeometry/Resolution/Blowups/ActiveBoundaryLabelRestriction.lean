import OAI.AlgebraicGeometry.Resolution.Blowups.OptionalBoundaryLabels

/-! # Active Boundary Label Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryLabelRestriction.Construction

noncomputable section

/-! Partial original-label restriction and exact divided sets for active boundaries. -/

universe u

def boundaryLabelRestriction {ι : Type u} (B : Finset ι) : ι → Option B := by
  classical
  exact fun j => if h : j ∈ B then some ⟨j, h⟩ else none

theorem boundaryLabelRestriction_distinct {ι : Type u} (B : Finset ι)
    (i j : ι) (s : B) (hi : boundaryLabelRestriction B i = some s)
    (hj : boundaryLabelRestriction B j = some s) : i = j := by
  classical
  by_cases hiB : i ∈ B
  · by_cases hjB : j ∈ B
    · simp only [boundaryLabelRestriction, dite_eq_left hiB, dite_eq_left hjB, Option.some.injEq] at hi hj
      exact congrArg Subtype.val (hi.trans hj.symm)
    · simp only [boundaryLabelRestriction, dite_eq_right hjB] at hj
      cases hj
  · simp only [boundaryLabelRestriction, dite_eq_right hiB] at hi
    cases hi

def restrictedBoundaryDividedLabels {ι : Type u} (B F : Finset ι) : Finset B := by
  classical
  exact Finset.univ.filter (fun j => j.val ∈ F)

theorem active_boundary_adjoined_divided_iff {ι : Type u} [DecidableEq ι]
    (B F : Finset ι) (hFB : F ⊆ B) (j : Option ι) :
    j ∈ insert none (F.image some) ↔
      ∃ s ∈ insert none ((restrictedBoundaryDividedLabels B F).image some),
        OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel (boundaryLabelRestriction B) j = some s := by
  classical
  cases j with
  | none => simp [OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel]
  | some j =>
      by_cases hj : j ∈ B
      · simp [OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, boundaryLabelRestriction, hj, restrictedBoundaryDividedLabels]
      · have hjF : j ∉ F := fun h => hj (hFB h)
        simp [OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, boundaryLabelRestriction, hj, hjF]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ActiveBoundaryLabelRestriction.Construction
