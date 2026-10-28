import OAI.Analysis.PDE.Concentration.Lattice.Faces
import OAI.Analysis.PDE.Concentration.Physical.Coordinates
import OAI.Analysis.PDE.Green.Physical.BoundaryTransfer

noncomputable section
namespace OAI.Analysis.PDE.Concentration

abbrev RealSlotCoordinates (d : ℕ) := Fin (d + 2) × Fin 3 → ℝ

/-- Change only the real spatial coordinates. Physical time and all complex
fiber coordinates remain fixed. The spatial map may encode a rotated lattice. -/
def spatialRealChange {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : RealSlotCoordinates d) (p : Fin (d + 2) × Fin 3) : ℝ :=
  if p.2 = 0 then Fin.cases (x (0, 0)) (fun i => L (fun j => x (j.succ, 0)) i) p.1
  else x p

@[simp] theorem spatialRealChange_time {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (x : RealSlotCoordinates d) :
    spatialRealChange L x (0, 0) = x (0, 0) := by simp [spatialRealChange]

@[simp] theorem spatialRealChange_spatial {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : RealSlotCoordinates d) (i : Fin (d + 1)) :
    spatialRealChange L x (i.succ, 0) = L (fun j => x (j.succ, 0)) i := by
  simp [spatialRealChange]

@[simp] theorem spatialRealChange_other {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : RealSlotCoordinates d) (i : Fin (d + 2)) (α : Fin 3) (hα : α ≠ 0) :
    spatialRealChange L x (i, α) = x (i, α) := by simp [spatialRealChange, hα]

def spatialRealLinearEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    RealSlotCoordinates d ≃ₗ[ℝ] RealSlotCoordinates d where
  toFun := spatialRealChange L
  invFun := spatialRealChange L.symm
  left_inv x := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    · simp [hα]
  right_inv x := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    · simp [hα]
  map_add' x y := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [spatialRealChange]
      · change L (fun k => x (k.succ, 0) + y (k.succ, 0)) j =
          L (fun k => x (k.succ, 0)) j + L (fun k => y (k.succ, 0)) j
        exact congrFun (L.map_add (fun k => x (k.succ, 0)) (fun k => y (k.succ, 0))) j
    · simp [spatialRealChange, hα]
  map_smul' c x := by
    funext ⟨i, α⟩
    by_cases hα : α = 0
    · subst α
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [spatialRealChange]
      · change L (fun k => c * x (k.succ, 0)) j = c * L (fun k => x (k.succ, 0)) j
        exact congrFun (L.map_smul c (fun k => x (k.succ, 0))) j
    · simp [spatialRealChange, hα]

def spatialRealEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    RealSlotCoordinates d ≃L[ℝ] RealSlotCoordinates d :=
  (spatialRealLinearEquiv L).toContinuousLinearEquiv

theorem spatialRealEquiv_apply {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (x : RealSlotCoordinates d) :
    spatialRealEquiv L x = spatialRealChange L x := rfl

def physicalLatticeEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 ≃L[ℝ]
      OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 2) × Fin 3 => ℝ)).trans
    ((spatialRealEquiv L).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 2) × Fin 3 => ℝ)).symm)

theorem physicalLatticeEquiv_apply {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (p : Fin (d + 2) × Fin 3) :
    physicalLatticeEquiv L x p = spatialRealChange L (fun q => x q) p := rfl

theorem fullPhysicalProjection_latticeEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.PDE.Green.fullPhysicalProjection d (physicalLatticeEquiv L x) =
      OAI.Analysis.PDE.Green.fullPhysicalProjection d x := by
  apply Prod.ext
  · change ((physicalLatticeEquiv L x (0, 1) : ℂ) +
      Complex.I * (physicalLatticeEquiv L x (0, 2) : ℂ)) = _
    simp only [physicalLatticeEquiv_apply]
    rfl
  · funext i
    change ((physicalLatticeEquiv L x (((finSuccEquiv d).symm i).succ, 1) : ℂ) +
      Complex.I * (physicalLatticeEquiv L x (((finSuccEquiv d).symm i).succ, 2) : ℂ)) = _
    simp only [physicalLatticeEquiv_apply]
    rfl

theorem physicalFullDefining_latticeEquiv {d : ℕ}
    (L : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (a : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.PDE.Green.physicalFullDefining d a (physicalLatticeEquiv L x) =
      OAI.Analysis.PDE.Green.physicalFullDefining d a x := by
  unfold OAI.Analysis.PDE.Green.physicalFullDefining
  rw [fullPhysicalProjection_latticeEquiv]

end OAI.Analysis.PDE.Concentration
