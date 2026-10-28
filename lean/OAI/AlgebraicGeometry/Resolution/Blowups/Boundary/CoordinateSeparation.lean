import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRelativeLine

/-! # Coordinate Separation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Retain all boundary labels while separating an unused coordinate as the normal. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)

/-- Boundary coordinates in the coefficient ring obtained by deleting
a coordinate used by none of the boundary labels. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoordinate (h : M.indices)
    (hh : ∀ j, M.coordinate j ≠ some h) (j : ι) : Option {t : M.indices // t ≠ h} :=
  (M.coordinate j).pmap (fun t ht => ⟨t, ht⟩)
    (fun _ hc ht => hh j (hc.trans (congrArg some ht)))

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoordinate_map (h : M.indices)
    (hh : ∀ j, M.coordinate j ≠ some h) (j : ι) :
    (M.separatedCoordinate h hh j).map Subtype.val = M.coordinate j := by
  cases hc : M.coordinate j <;> simp [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoordinate, hc]

/-- The normalized coefficient equations are distinct polynomial
coordinates or units, with the original labels retained. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoefficientModel (h : M.indices)
    (hh : ∀ j, M.coordinate j ≠ some h) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (MvPolynomialRelativeLine.Construction.coordinateLineBase (k := k) h) ι
      (fun j => match M.separatedCoordinate h hh j with
        | none => 1 | some t => MvPolynomial.X t) := by
  classical
  refine
    { indices := {t : M.indices // t ≠ h}
      finite := inferInstance
      decidableEq := inferInstance
      map := RingHom.id _
      etale := RingHom.Etale.of_bijective Function.bijective_id
      ground := fun _ => rfl
      coordinate := M.separatedCoordinate h hh
      distinct := ?_
      multiplier := fun _ => 1
      multiplierUnit := fun _ => isUnit_one
      equation := ?_ }
  · intro i j t hi hj
    apply M.distinct i j t.val
    · rw [← M.separatedCoordinate_map h hh i, hi]
      rfl
    · rw [← M.separatedCoordinate_map h hh j, hj]
      rfl
  · intro j
    cases M.separatedCoordinate h hh j <;> exact (one_mul _).symm

/-- Before taking the hypersurface, the original equation is exactly
its ambient unit factor times the retained coefficient equation. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.separated_equation (h : M.indices)
    (hh : ∀ j, M.coordinate j ≠ some h) (j : ι) :
    w j = M.multiplier j * M.map ((MvPolynomialRelativeLine.Construction.coordinateLineEquiv (k := k) h).symm
      (Polynomial.C (match M.separatedCoordinate h hh j with
        | none => 1 | some t => MvPolynomial.X t))) := by
  rw [M.equation j]
  congr 1
  cases hc : M.coordinate j with
  | none => simp [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoordinate, hc]
  | some t =>
      simp only [Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.separatedCoordinate, hc, Option.pmap_some]
      rw [MvPolynomialRelativeLine.Construction.coordinateLineEquiv_symm_other]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
