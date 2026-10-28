import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Blowup Coordinate Labels -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupCoordinateLabels.Construction

noncomputable section

/-! Keep old boundary labels distinct from the new exceptional label. -/

universe u v

variable {ι : Type v} {σ : Type u} [DecidableEq σ]

/-- `none` labels the new exceptional divisor. The old denominator
component is removed, and every other old label keeps its coordinate. -/
def blownBoundaryCoordinate (e : ι ↪ σ) (i : σ) : Option ι → Option σ
  | none => some i
  | some j => if e j = i then none else some (e j)

theorem blownBoundaryCoordinate_distinct (e : ι ↪ σ) (i : σ)
    (x y : Option ι) (s : σ)
    (hx : blownBoundaryCoordinate e i x = some s)
    (hy : blownBoundaryCoordinate e i y = some s) : x = y := by
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y =>
          simp only [blownBoundaryCoordinate, Option.some.injEq] at hx
          simp only [blownBoundaryCoordinate] at hy
          by_cases h : e y = i
          · rw [ite_eq_left h] at hy
            cases hy
          · rw [ite_eq_right h] at hy
            exact False.elim (h ((Option.some.inj hy).trans hx.symm))
  | some x =>
      cases y with
      | none =>
          simp only [blownBoundaryCoordinate, Option.some.injEq] at hy
          simp only [blownBoundaryCoordinate] at hx
          by_cases h : e x = i
          · rw [ite_eq_left h] at hx
            cases hx
          · rw [ite_eq_right h] at hx
            exact False.elim (h ((Option.some.inj hx).trans hy.symm))
      | some y =>
          simp only [blownBoundaryCoordinate] at hx hy
          by_cases hx' : e x = i
          · rw [ite_eq_left hx'] at hx
            cases hx
          · rw [ite_eq_right hx'] at hx
            by_cases hy' : e y = i
            · rw [ite_eq_left hy'] at hy
              cases hy
            · rw [ite_eq_right hy'] at hy
              exact congrArg some (e.injective ((Option.some.inj hx).trans (Option.some.inj hy).symm))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupCoordinateLabels.Construction
