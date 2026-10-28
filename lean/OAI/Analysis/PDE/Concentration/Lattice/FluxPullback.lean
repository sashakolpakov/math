import OAI.Analysis.PDE.Concentration.Lattice.Periodicity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.PDE.Green

def pulledLatticeFlux {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (F : ι → EuclideanSpace ℝ ι → ℝ) (p : ι) (x : EuclideanSpace ℝ ι) : ℝ :=
  linearPiola L (latticeCoordinateField c F) (OAI.Analysis.PDE.Green.euclideanCoordinates c x) (c p)

theorem compatibleLatticeFaces_iff_pullback {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (r : EuclideanSpace ℝ ι → ℝ)
    (F : ι → EuclideanSpace ℝ ι → ℝ) :
    CompatibleLatticeFaces c L a b r F ↔
      OAI.Analysis.PDE.Green.CompatibleCellFaces c a b
        (fun x => r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (OAI.Analysis.PDE.Green.euclideanCoordinates c x))))
        (pulledLatticeFlux c L F) := by
  simp only [CompatibleLatticeFaces, OAI.Analysis.PDE.Green.CompatibleCellFaces, pulledLatticeFlux,
    ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem pulledLatticeFlux_periodic {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (F : ι → EuclideanSpace ℝ ι → ℝ) (w : EuclideanSpace ℝ ι)
    (hF : ∀ p x, F p (x + (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (OAI.Analysis.PDE.Green.euclideanCoordinates c w))) = F p x)
    (p : ι) (x : EuclideanSpace ℝ ι) :
    pulledLatticeFlux c L F p (x + w) = pulledLatticeFlux c L F p x := by
  have hp (y : Fin (m + 1) → ℝ) :
      latticeCoordinateField c F (y + L (OAI.Analysis.PDE.Green.euclideanCoordinates c w)) = latticeCoordinateField c F y := by
    funext j
    simp only [latticeCoordinateField, map_add]
    exact hF _ _
  simp only [pulledLatticeFlux, map_add]
  exact congrFun (linearPiola_add_period L (latticeCoordinateField c F) _ hp _) (c p)

theorem pulledLatticeFlux_zero {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (F : ι → EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (hF : ∀ p, F p ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (OAI.Analysis.PDE.Green.euclideanCoordinates c x))) = 0)
    (p : ι) : pulledLatticeFlux c L F p x = 0 := by
  have hz : latticeCoordinateField c F (L (OAI.Analysis.PDE.Green.euclideanCoordinates c x)) = 0 := funext (fun j => hF _)
  simp only [pulledLatticeFlux, linearPiola, Function.comp_apply, hz, map_zero, Pi.zero_apply]

end OAI.Analysis.PDE.Concentration
