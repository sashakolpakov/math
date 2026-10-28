import OAI.Analysis.PDE.Weak.Boundary.RegularityAlgebra

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem FunctionWeakRegularity.component {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} (hu : FunctionWeakRegularity Ω k u)
    (j : Fin (m + 1)) : FunctionWeakRegularity Ω k (fun x => u x j) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  exact hu.map ((ContinuousLinearMap.proj j).comp e)

theorem FunctionWeakRegularity.of_components {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m}
    (hu : ∀ j, FunctionWeakRegularity Ω k (fun x => u x j)) :
    FunctionWeakRegularity Ω k u := by
  let L (j : Fin (m + 1)) : ℝ →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j 1)
  have hh := OAI.Analysis.PDE.Weak.FunctionWeakRegularity.finset_sum Finset.univ
    (fun j x => L j (u x j)) (fun j _ => (hu j).map (L j))
  apply hh.congr_on
  filter_upwards with x
  intro _
  change (∑ j, u x j • EuclideanSpace.single j 1) = u x
  ext j
  simp [Pi.single_apply]

end OAI.Analysis.PDE.Weak
