import OAI.Analysis.PDE.Weak.Boundary.SmoothBounded
import OAI.Analysis.PDE.Weak.Boundary.OperatorEntries

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem smoothBounded_realOperatorEntry
    {A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m}
    (hA : SmoothBounded A) (i j : Fin (m+1)) :
    SmoothBounded (fun x => realOperatorEntry (A x) i j) := by
  let pr : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  let ev : (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
    ContinuousLinearMap.apply ℝ (OAI.Analysis.PDE.Variational.CellVectors m) (EuclideanSpace.single j 1)
  exact hA.map (pr.comp ev)

end OAI.Analysis.PDE.Weak
