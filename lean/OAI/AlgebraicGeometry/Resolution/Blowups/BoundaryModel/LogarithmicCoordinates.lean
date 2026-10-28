import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicUnitEquations

/-! # Logarithmic Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Express logarithmic differential ideals of actual boundary equations in their model coordinates. -/

universe u v

variable {k A : Type u} {ι : Type v} [CommRing k] [CommRing A] [Algebra k A]
  {w : ι → A}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) (j : ι) : A :=
  match M.coordinate j with
  | none => 1
  | some s => M.map (MvPolynomial.X s)

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryIndices (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) : Finset M.indices := by
  classical
  exact Finset.univ.filter (fun s => ∃ j, M.coordinate j = some s)

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.mem_boundaryIndices (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) (s : M.indices) :
    s ∈ M.boundaryIndices ↔ ∃ j, M.coordinate j = some s := by
  classical
  simp only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.boundaryIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.logarithmic_coordinateEquation (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) :
    Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w = Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k M.coordinateEquation := by
  have he : w = fun j => M.multiplier j * M.coordinateEquation j := by
    funext j
    rw [M.equation j]
    congr 1
    cases h : M.coordinate j <;> simp only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, h]
  exact (congrArg (Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k) he).trans
    (LogarithmicUnitEquations.Construction.relativeLogarithmicDerivations_mul_units k M.coordinateEquation M.multiplier M.multiplierUnit)

/-- Unit components contribute no tangency condition, and each remaining
actual equation contributes exactly its corresponding coordinate ideal. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.logarithmic_coordinates (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) :
    Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w = Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun s : M.boundaryIndices => M.map (MvPolynomial.X s.val)) := by
  rw [M.logarithmic_coordinateEquation]
  ext D
  change (∀ j, D (M.coordinateEquation j) ∈ Ideal.span {M.coordinateEquation j}) ↔
    ∀ s : M.boundaryIndices, D (M.map (MvPolynomial.X s.val)) ∈ Ideal.span {M.map (MvPolynomial.X s.val)}
  constructor
  · intro h s
    obtain ⟨j, hj⟩ := (M.mem_boundaryIndices s.val).mp s.property
    simpa only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hj] using h j
  · intro h j
    cases hj : M.coordinate j with
    | none => simp [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hj]
    | some s =>
        have hs : s ∈ M.boundaryIndices := (M.mem_boundaryIndices s).mpr ⟨j, hj⟩
        simpa only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hj] using h ⟨s, hs⟩

/-- Every order of the relative logarithmic differential ideal agrees
exactly with the finite coordinate boundary in the displayed model. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.iterated_logarithmic_coordinates (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w)
    (J : Ideal A) (n : ℕ) :
    Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n =
      Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
        (fun s : M.boundaryIndices => M.map (MvPolynomial.X s.val)) J n :=
  Relative.LogarithmicBoundary.Construction.iteratedRelativeLogarithmicDifferentialIdeal_congr_derivations k _ _ M.logarithmic_coordinates J n

end

end OAI.AlgebraicGeometry.Resolution.Blowups
