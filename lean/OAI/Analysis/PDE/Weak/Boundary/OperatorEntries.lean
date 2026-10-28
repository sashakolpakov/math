import OAI.Analysis.PDE.Weak.Boundary.Weak.Vector

/-! Entrywise properties inherited from the actual real elliptic operator,
for use in normal derivative recovery. -/

noncomputable section
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

def realOperatorEntry (A : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (i j : Fin (m + 1)) : ℝ := A (EuclideanSpace.single j 1) i

theorem realOperatorEntry_norm_le (A : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (i j) :
    ‖realOperatorEntry A i j‖ ≤ ‖A‖ := by
  exact (PiLp.norm_apply_le _ i).trans (by simpa using A.le_opNorm (EuclideanSpace.single j 1))

theorem realOperatorEntry_apply (A : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (v : OAI.Analysis.PDE.Variational.CellVectors m) (i) :
    A v i = ∑ j, realOperatorEntry A i j * v j := by
  have hv : v = ∑ j, v j • EuclideanSpace.single j 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  let pr : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  change pr (∑ j, A (v j • EuclideanSpace.single j 1)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, pr, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, realOperatorEntry, mul_comm]
  rfl

theorem realOperatorEntry_diagonal_lower (A : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) {lam : ℝ}
    (hell : ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A z) z) (k) :
    lam ≤ realOperatorEntry A k k := by
  simpa [realOperatorEntry, EuclideanSpace.inner_single_right] using hell (EuclideanSpace.single k 1)

theorem contDiff_realOperatorEntry
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    {n : ℕ∞ω} (hA : ContDiff ℝ n A) (i j) :
    ContDiff ℝ n (fun x => realOperatorEntry (A x) i j) := by
  let pr : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  exact pr.contDiff.comp (hA.clm_apply contDiff_const)

theorem fderiv_realOperatorEntry
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) (i j) (x v : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    fderiv ℝ (fun y => realOperatorEntry (A y) i j) x v =
      realOperatorEntry (fderiv ℝ A x v) i j := by
  let pr : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  have h := (pr.hasFDerivAt.comp x
    ((hA.differentiable one_ne_zero x).hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.single j 1) x))).fderiv
  change fderiv ℝ (fun y => realOperatorEntry (A y) i j) x = _ at h
  simpa [realOperatorEntry, pr] using congrArg (fun L => L v) h

theorem realOperatorEntry_derivative_norm_le
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m)
    (hA : ContDiff ℝ 1 A) (i j l) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    ‖fderiv ℝ (fun y => realOperatorEntry (A y) i j) x (Pi.single l 1)‖ ≤ ‖fderiv ℝ A x‖ := by
  rw [fderiv_realOperatorEntry A hA]
  exact (realOperatorEntry_norm_le _ i j).trans
    (by simpa [Pi.norm_single] using (fderiv ℝ A x).le_opNorm (Pi.single l 1))

end OAI.Analysis.PDE.Weak
