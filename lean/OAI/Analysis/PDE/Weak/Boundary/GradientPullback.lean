import OAI.Analysis.PDE.Weak.Boundary.Weak.Coordinates
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual gradient transformation associated to a boundary chart. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def chartGradientMap (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      innerSL ℝ (WithLp.toLp 2 (fderiv ℝ G x (Pi.single i 1)))))

theorem chartGradientMap_apply (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (v : OAI.Analysis.PDE.Variational.CellVectors m) (i : Fin (m + 1)) :
    chartGradientMap G x v i = inner ℝ v (WithLp.toLp 2 (fderiv ℝ G x (Pi.single i 1))) := by
  simp [chartGradientMap, real_inner_comm]

theorem continuous_chartGradientMap {G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ 1 G) : Continuous (chartGradientMap G) := by
  have hd : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have hp : Continuous (fun x => ContinuousLinearMap.pi (fun i : Fin (m + 1) =>
      innerSL ℝ (WithLp.toLp 2 (fderiv ℝ G x (Pi.single i 1))))) :=
    (ContinuousLinearMap.piEquivL ℝ (OAI.Analysis.PDE.Variational.CellVectors m) (fun _ : Fin (m + 1) => ℝ)).continuous.comp
      (by fun_prop)
  unfold chartGradientMap
  fun_prop

theorem cellGradient_comp_chart {G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : DifferentiableAt ℝ G x) (hu : DifferentiableAt ℝ u (G x)) :
    OAI.Analysis.PDE.Variational.cellGradient (u ∘ G) x = chartGradientMap G x (OAI.Analysis.PDE.Variational.cellGradient u (G x)) := by
  ext i
  rw [chartGradientMap_apply]
  change fderiv ℝ (u ∘ G) x (Pi.single i 1) = _
  rw [(hu.hasFDerivAt.comp x hG.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact fderiv_eq_cellGradient_pairing u (G x)
    (WithLp.toLp 2 (fderiv ℝ G x (Pi.single i 1))) |>.trans (real_inner_comm _ _)

end OAI.Analysis.PDE.Weak
