import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Coordinate Lift Choice -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateLiftChoice.Construction

noncomputable section

/-! Choose lifts of quotient coordinates that retain exact ambient boundary equations. -/

universe u v

theorem exists_boundary_preserving_coordinate_lifts
    {R Q : Type u} [CommRing R] [CommRing Q] (q : R →+* Q) (hq : Function.Surjective q)
    {ι : Type u} {β : Type v} (x : ι → Q) (w a : β → R) (ha : ∀ j, IsUnit (a j))
    (e : β → Option ι) (he : ∀ i j s, e i = some s → e j = some s → i = j)
    (hw : ∀ j, q (w j) = q (a j) * match e j with | none => 1 | some i => x i)
    (hnone : ∀ j, e j = none → w j = a j) :
    ∃ g : ι → R, (∀ i, q (g i) = x i) ∧
      ∀ j, w j = a j * match e j with | none => 1 | some i => g i := by
  classical
  choose v hv using fun i => hq (x i)
  let g (i : ι) : R := if h : ∃ j, e j = some i then
    ↑((ha h.choose).unit⁻¹) * w h.choose else v i
  have hg (i : ι) : q (g i) = x i := by
    dsimp only [g]
    split_ifs with h
    · rw [map_mul, hw, h.choose_spec]
      change q (↑((ha h.choose).unit⁻¹)) * (q (a h.choose) * x i) = x i
      have hunit : ↑((ha h.choose).unit⁻¹) * a h.choose = 1 := by
        simpa only [(ha h.choose).unit_spec] using (ha h.choose).unit.inv_mul
      rw [← mul_assoc, ← map_mul, hunit, map_one, one_mul]
    · exact hv i
  refine ⟨g, hg, ?_⟩
  intro j
  cases hj : e j with
  | none => rw [hnone j hj, mul_one]
  | some i =>
      change w j = a j * g i
      have h : ∃ l, e l = some i := ⟨j, hj⟩
      have hj' : h.choose = j := he h.choose j i h.choose_spec hj
      have hgi : g i = ↑((ha j).unit⁻¹) * w j := by
        dsimp only [g]
        rw [dite_eq_left h, hj']
      have hunit : a j * ↑((ha j).unit⁻¹) = 1 := by
        simpa only [(ha j).unit_spec] using (ha j).unit.mul_inv
      rw [hgi, ← mul_assoc, hunit, one_mul]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateLiftChoice.Construction
