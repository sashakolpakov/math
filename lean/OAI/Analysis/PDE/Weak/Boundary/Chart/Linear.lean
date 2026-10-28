import OAI.Analysis.PDE.Weak.Boundary.GradientPullback

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A coordinate linear map expressed in the Euclidean gradient space. -/
def coordinateTangentMap (T : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).symm.toContinuousLinearMap.comp
    (T.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).toContinuousLinearMap)

theorem coordinateTangentMap_apply (T : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m)
    (v : OAI.Analysis.PDE.Variational.CellVectors m) : coordinateTangentMap T v = WithLp.toLp 2 (T (WithLp.ofLp v)) := rfl

theorem coordinateTangentMap_comp (T S : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m) :
    coordinateTangentMap (T.comp S) = (coordinateTangentMap T).comp (coordinateTangentMap S) := by
  ext v i
  rfl

theorem coordinateTangentMap_id :
    coordinateTangentMap (ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellCoordinates m)) =
      ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Variational.CellVectors m) := by
  ext v i
  rfl

theorem chartGradientMap_eq_adjoint (G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    chartGradientMap G x = (coordinateTangentMap (fderiv ℝ G x)).adjoint := by
  ext v i
  rw [chartGradientMap_apply]
  have h := (coordinateTangentMap (fderiv ℝ G x)).adjoint_inner_left (EuclideanSpace.single i 1) v
  simpa [coordinateTangentMap_apply, EuclideanSpace.inner_single_right] using h.symm

theorem chartGradientMap_inverse
    {U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (_ : IsOpen U) (hV : IsOpen V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m} (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hGU : MapsTo G U V) (hPG : ∀ y ∈ U, P (G y) = y) (hGP : ∀ z ∈ V, G (P z) = z)
    {y : OAI.Analysis.PDE.Variational.CellCoordinates m} (hy : y ∈ U) :
    (chartGradientMap P (G y)).comp (chartGradientMap G y) = ContinuousLinearMap.id ℝ _ := by
  have he : (fun z => G (P z)) =ᶠ[𝓝 (G y)] id := by
    filter_upwards [hV.mem_nhds (hGU hy)] with z hz
    exact hGP z hz
  have hd := ((hG.differentiable one_ne_zero (P (G y))).hasFDerivAt.comp (G y)
    (hP.differentiable one_ne_zero (G y)).hasFDerivAt).fderiv
  rw [hPG y hy] at hd
  have hJ : (fderiv ℝ G y).comp (fderiv ℝ P (G y)) = ContinuousLinearMap.id ℝ _ := by
    simpa using hd.symm.trans he.fderiv_eq
  rw [chartGradientMap_eq_adjoint, chartGradientMap_eq_adjoint, ← ContinuousLinearMap.adjoint_comp,
    ← coordinateTangentMap_comp, hJ, coordinateTangentMap_id]
  exact ContinuousLinearMap.adjoint_id

theorem chart_fderiv_inverse
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m} (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hPG : ∀ y ∈ U, P (G y) = y) {y : OAI.Analysis.PDE.Variational.CellCoordinates m} (hy : y ∈ U) :
    (fderiv ℝ P (G y)).comp (fderiv ℝ G y) = ContinuousLinearMap.id ℝ _ := by
  have he : (fun z => P (G z)) =ᶠ[𝓝 y] id := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hPG z hz
  have hd := ((hP.differentiable one_ne_zero (G y)).hasFDerivAt.comp y
    (hG.differentiable one_ne_zero y).hasFDerivAt).fderiv
  simpa using hd.symm.trans he.fderiv_eq

theorem chartGradientMap_inverse_other
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m} (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hPG : ∀ y ∈ U, P (G y) = y) {y : OAI.Analysis.PDE.Variational.CellCoordinates m} (hy : y ∈ U) :
    (chartGradientMap G y).comp (chartGradientMap P (G y)) = ContinuousLinearMap.id ℝ _ := by
  rw [chartGradientMap_eq_adjoint, chartGradientMap_eq_adjoint, ← ContinuousLinearMap.adjoint_comp,
    ← coordinateTangentMap_comp, chart_fderiv_inverse hU hG hP hPG hy, coordinateTangentMap_id]
  exact ContinuousLinearMap.adjoint_id

theorem chartJacobian_ne_zero
    {U : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m} (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hPG : ∀ y ∈ U, P (G y) = y) {y : OAI.Analysis.PDE.Variational.CellCoordinates m} (hy : y ∈ U) :
    (fderiv ℝ G y).det ≠ 0 := by
  have hd := congrArg (fun T : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] OAI.Analysis.PDE.Variational.CellCoordinates m => T.det)
    (chart_fderiv_inverse hU hG hP hPG hy)
  change LinearMap.det ((fderiv ℝ P (G y)).toLinearMap.comp (fderiv ℝ G y).toLinearMap) =
    LinearMap.det LinearMap.id at hd
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  exact right_ne_zero_of_mul_eq_one hd

end OAI.Analysis.PDE.Weak
