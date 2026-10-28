import OAI.Analysis.PDE.Weak.Boundary.Weak.Pullback
import OAI.Analysis.PDE.Weak.Elliptic.TestSupport

/-! Identification of coordinate-gradient weak equations with the
coordinate-free flux equation used for boundary changes of variables. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem fderiv_eq_cellGradient_pairing (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) (v : OAI.Analysis.PDE.Variational.CellVectors m) :
    fderiv ℝ u x (WithLp.ofLp v) = inner ℝ v (OAI.Analysis.PDE.Variational.cellGradient u x) := by
  have hv : WithLp.ofLp v = ∑ i : Fin (m + 1), v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  simp [PiLp.inner_apply, OAI.Analysis.PDE.Variational.cellGradient, RCLike.inner_apply, mul_comm]

theorem weakDivergenceEquation_iff_weakFluxEquation
    (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m)
    (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) :
    WeakDivergenceEquation Ω H f ↔
      WeakFluxEquation volume Ω (fun x => WithLp.ofLp (H x)) f := by
  unfold WeakDivergenceEquation WeakFluxEquation
  simp only [fderiv_eq_cellGradient_pairing]

end OAI.Analysis.PDE.Weak
