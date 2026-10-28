import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Coordinates

/-! # Optional Boundary Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Insert the new exceptional label while retaining all original unit and coordinate labels. -/

universe u v t

def OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel {ι : Type v} {κ : Type t} (c : ι → Option κ) :
    Option ι → Option (Option κ)
  | none => some none
  | some j => (c j).map some

theorem OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel_distinct {ι : Type v} {κ : Type t} (c : ι → Option κ)
    (hc : ∀ i j s, c i = some s → c j = some s → i = j)
    (i j : Option ι) (s : Option κ)
    (hi : OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel c i = some s)
    (hj : OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel c j = some s) : i = j := by
  cases i with
  | none =>
      have hs : s = none := Option.some.inj hi.symm
      subst s
      cases j with
      | none => rfl
      | some j =>
          change (c j).map some = some none at hj
          cases h : c j <;> simp [h] at hj
  | some i =>
      cases j with
      | none =>
          have hs : s = none := Option.some.inj hj.symm
          subst s
          change (c i).map some = some none at hi
          cases h : c i <;> simp [h] at hi
      | some j =>
          change (c i).map some = some s at hi
          change (c j).map some = some s at hj
          cases hci : c i with
          | none => simp only [hci, Option.map_none] at hi; cases hi
          | some a =>
              cases hcj : c j with
              | none => simp only [hcj, Option.map_none] at hj; cases hj
              | some b =>
                  have hi' : some a = s := by simpa only [hci, Option.map_some, Option.some.injEq] using hi
                  have hj' : some b = s := by simpa only [hcj, Option.map_some, Option.some.injEq] using hj
                  have hab : b = a := Option.some.inj (hj'.trans hi'.symm)
                  exact congrArg some (hc i j a hci (hcj.trans (congrArg some hab)))

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryCoordinate_distinct
    {k R : Type u} {ι : Type v} [CommRing k] [CommRing R] [Algebra k R]
    {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (i j : ι) (s : M.boundaryIndices)
    (hi : M.boundaryCoordinate i = some s) (hj : M.boundaryCoordinate j = some s) : i = j := by
  apply M.distinct i j s.val
  · rw [← M.boundaryCoordinate_map i, hi]
    rfl
  · rw [← M.boundaryCoordinate_map j, hj]
    rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
