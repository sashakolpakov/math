import OAI.Analysis.PDE.Weak.Elliptic.Classical.Equation

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem cellGradient_eventuallyEq {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (h : u =ᶠ[𝓝 x] v) : OAI.Analysis.PDE.Variational.cellGradient u =ᶠ[𝓝 x] OAI.Analysis.PDE.Variational.cellGradient v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  ext i
  exact congrArg (fun L : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ ↦ L (Pi.single i 1)) hy

theorem classicalDivergence_congr_of_eventuallyEq
    {H K : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (h : H =ᶠ[𝓝 x] K) : classicalDivergence H x = classicalDivergence K x := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y ↦ H y i) =ᶠ[𝓝 x] fun y ↦ K y i :=
    h.mono fun y hy ↦ congrArg (fun z : OAI.Analysis.PDE.Variational.CellVectors m ↦ z i) hy
  exact congrArg (fun L : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ ↦ L (Pi.single i 1)) hi.fderiv_eq

theorem classical_elliptic_operator_congr
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    {u v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m} (h : u =ᶠ[𝓝 x] v) :
    classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient u y)) x =
      classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x := by
  apply classicalDivergence_congr_of_eventuallyEq
  exact (cellGradient_eventuallyEq h).mono fun y hy ↦ congrArg (A y) hy

end OAI.Analysis.PDE.Weak
