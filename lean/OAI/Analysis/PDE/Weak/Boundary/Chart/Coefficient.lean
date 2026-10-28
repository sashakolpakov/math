import OAI.Analysis.PDE.Weak.Boundary.Chart.Linear
import OAI.Analysis.PDE.Green.JacobianSmooth

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem contDiff_chartGradientMap {G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (chartGradientMap G) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
  have hp : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.pi (fun i : Fin (m+1) =>
      innerSL ℝ (WithLp.toLp 2 (fderiv ℝ G x (Pi.single i 1))))) :=
    (ContinuousLinearMap.piEquivL ℝ (OAI.Analysis.PDE.Variational.CellVectors m) (fun _ : Fin (m+1) => ℝ)).contDiff.comp
      (by
        apply contDiff_pi.mpr
        intro i
        exact (innerSL ℝ : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ).contDiff.comp
          (by fun_prop))
  unfold chartGradientMap
  fun_prop

/-- The genuine symmetric divergence-form coefficient transported through
a chart. The scalar weight will be the absolute Jacobian locally. -/
def chartCoefficient (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (y : OAI.Analysis.PDE.Variational.CellCoordinates m) : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  w y • (chartGradientMap P (G y)).adjoint.comp
    ((A (G y)).comp (chartGradientMap P (G y)))

theorem chartCoefficient_form (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m) (w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (y : OAI.Analysis.PDE.Variational.CellCoordinates m) (v : OAI.Analysis.PDE.Variational.CellVectors m) :
    inner ℝ (chartCoefficient A G P w y v) v =
      w y * inner ℝ (A (G y) (chartGradientMap P (G y) v))
        (chartGradientMap P (G y) v) := by
  simp only [chartCoefficient, smul_apply, ContinuousLinearMap.comp_apply,
    real_inner_smul_left]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem contDiff_chartCoefficient
    {A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m}
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m} {w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (chartCoefficient A G P w) := by
  have hC := (contDiff_chartGradientMap hP).comp hG
  have hCA : ContDiff ℝ ∞ (fun y => (chartGradientMap P (G y)).adjoint) :=
    (ContinuousLinearMap.adjoint : (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) ≃ₗᵢ[ℝ]
      (OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)).contDiff.comp hC
  unfold chartCoefficient
  fun_prop

theorem contDiff_chartJacobian {G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (fun y => (fderiv ℝ G y).det) :=
  (OAI.Analysis.PDE.Green.contDiff_continuousLinearMap_det (OAI.Analysis.PDE.Variational.CellCoordinates m) ∞).comp
    (hG.fderiv_right (by simp))

end OAI.Analysis.PDE.Weak
