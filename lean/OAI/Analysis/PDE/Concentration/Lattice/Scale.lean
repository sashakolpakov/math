import OAI.Analysis.PDE.Concentration.Lattice.Chart

noncomputable section
namespace OAI.Analysis.PDE.Concentration

/-- The manuscript's side-100 period map in an arbitrary fixed spatial frame.
The frame need not align with any coordinate axis of the energy calculation. -/
def sideHundredLattice {d : ℕ}
    (R : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) :=
  R.trans ((LinearEquiv.smulOfNeZero ℝ (Fin (d + 1) → ℝ) 100 (by norm_num)).toContinuousLinearEquiv)

@[simp] theorem sideHundredLattice_apply {d : ℕ}
    (R : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (x : Fin (d + 1) → ℝ) :
    sideHundredLattice R x = (100 : ℝ) • R x := rfl

theorem sideHundredLattice_period {d : ℕ}
    (R : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ)) (i : Fin (d + 1)) :
    sideHundredLattice R (Pi.single i 1) = (100 : ℝ) • R (Pi.single i 1) := rfl

theorem sideHundred_physical_defining {d : ℕ}
    (R : (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ))
    (a : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    OAI.Analysis.PDE.Green.physicalFullDefining d a
      (physicalLatticeEquiv (sideHundredLattice R) x) =
        OAI.Analysis.PDE.Green.physicalFullDefining d a x :=
  physicalFullDefining_latticeEquiv _ _ _

end OAI.Analysis.PDE.Concentration
