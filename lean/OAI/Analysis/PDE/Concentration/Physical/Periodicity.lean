import OAI.Analysis.PDE.Concentration.Physical.LatticeCurrent

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Matrix

/-- Negative physical spatial translation, as used by convolution. -/
def physicalSpatialTranslate {d : ℕ} (y : OAI.Analysis.Calculus.Current.SpatialSpace d) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 2) × Fin 3 => ℝ)).symm
    (fun p => if p.2 = 0 then Fin.cases 0 (fun j => -y (finSuccEquiv d j)) p.1 else 0)

@[simp] theorem physicalSpatialTranslate_time {d : ℕ} (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    physicalSpatialTranslate y (0, 0) = 0 := rfl

@[simp] theorem physicalSpatialTranslate_spatial {d : ℕ}
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (j : Fin (d + 1)) :
    physicalSpatialTranslate y (j.succ, 0) = -y (finSuccEquiv d j) := rfl

@[simp] theorem physicalSpatialTranslate_imaginary {d : ℕ}
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (i : Fin (d + 2)) (α : Fin 3) (hα : α ≠ 0) :
    physicalSpatialTranslate y (i, α) = 0 := by
  change (if α = 0 then _ else 0) = 0
  simp [hα]

theorem physicalToNullCurrentPoint_add {d : ℕ} (x y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalToNullCurrentPoint d (x + y) = physicalToNullCurrentPoint d x +
      physicalToNullCurrentPoint d y := by
  simp only [physicalToNullCurrentPoint, map_add]

theorem physicalToNullCurrentPoint_spatialTranslate {d : ℕ} (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    physicalToNullCurrentPoint d (physicalSpatialTranslate y) = (nullSpatialShift y, 0) := by
  apply Prod.ext
  · funext i
    change (nullCoordinateProjection d
      (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) (physicalSpatialTranslate y))).1 i = _
    rw [nullCoordinateProjection_real]
    cases i with
    | none =>
      rw [nullIndexEquiv_symm_none, nullRotation_action_time]
      change (0 + -y none) / Real.sqrt 2 = -y none / Real.sqrt 2
      rw [zero_add]
    | some i =>
      cases i with
      | none =>
        rw [nullIndexEquiv_symm_some_none, nullRotation_action_longitudinal]
        change (-y none - 0) / Real.sqrt 2 = -y none / Real.sqrt 2
        rw [sub_zero]
      | some i =>
        rw [nullIndexEquiv_symm_some_some, nullRotation_action_transverse]
        simp [physicalSpatialTranslate, nullSpatialShift]
  · funext i
    change (nullCoordinateProjection d
      (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) (physicalSpatialTranslate y))).2 i = 0
    rw [nullCoordinateProjection_imaginary]
    cases i with
    | none => simp [nullRotation_action_time]
    | some i => cases i <;> simp [nullRotation_action_longitudinal, nullRotation_action_transverse]

theorem physicalLatticeCurrent_periodic {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (hy : ∀ j, ∃ k : ℤ, OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector (κ j) (v j)) (nullSpatialShift y) =
      (k : ℝ) * (2 * Real.pi)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalLatticeCurrent R h a κ cR cI v (x + physicalSpatialTranslate y) =
      physicalLatticeCurrent R h a κ cR cI v x := by
  simp only [physicalLatticeCurrent_eq_physicalMatrix, physicalToNullCurrentPoint_add,
    physicalToNullCurrentPoint_spatialTranslate, Prod.fst_add, Prod.snd_add, add_zero]
  rw [latticeRegularizedCurrent_periodic R h a κ cR cI v _ hy]

end OAI.Analysis.PDE.Concentration
