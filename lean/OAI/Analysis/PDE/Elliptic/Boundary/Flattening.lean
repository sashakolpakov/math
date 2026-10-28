import OAI.Analysis.PDE.Dirichlet.LevelSet
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A genuine boundary-flattening chart obtained from the inverse function
theorem.  Its differential at the base point is the identity. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def flatteningMap (r : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) (w : E) (y : E) : E :=
  (y - x) + (r y - r x - g (y - x)) • w

theorem flatteningMap_base (r : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) (w : E) :
    flatteningMap r x g w x = 0 := by simp [flatteningMap]

theorem flatteningMap_level (r : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) (w : E)
    (hw : g w = 1) (y : E) : g (flatteningMap r x g w y) = r y - r x := by
  simp only [flatteningMap, map_add, map_smul, hw, smul_eq_mul, mul_one]
  ring

theorem contDiff_flatteningMap {r : E → ℝ} {n : WithTop ℕ∞}
    (hr : ContDiff ℝ n r) (x : E) (g : E →L[ℝ] ℝ) (w : E) :
    ContDiff ℝ n (flatteningMap r x g w) := by
  exact (contDiff_id.sub contDiff_const).add
    (((hr.sub contDiff_const).sub (g.contDiff.comp (contDiff_id.sub contDiff_const))).smul contDiff_const)

theorem hasFDerivAt_flatteningMap {r : E → ℝ} {x : E} {g : E →L[ℝ] ℝ}
    (hr : HasFDerivAt r g x) (w : E) :
    HasFDerivAt (flatteningMap r x g w) (ContinuousLinearMap.id ℝ E) x := by
  have hid : HasFDerivAt (fun y : E => y - x) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id x).sub_const x
  have hg : HasFDerivAt (fun y : E => g (y - x)) g x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using g.hasFDerivAt.comp x hid
  have hz : HasFDerivAt (fun y => r y - r x - g (y - x)) (0 : E →L[ℝ] ℝ) x := by
    simpa using! (hr.sub_const (r x)).sub hg
  have h := hid.add (hz.smul_const w)
  change HasFDerivAt (flatteningMap r x g w)
    (ContinuousLinearMap.id ℝ E + (0 : E →L[ℝ] ℝ).smulRight w) x at h
  simpa using h

/-- Near every regular level point there is a C³ inverse chart taking the
linear half-space exactly to the original sublevel domain. -/
theorem exists_boundary_flattening [CompleteSpace E]
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (x : E) (hg : fderiv ℝ r x ≠ 0) :
    ∃ (w : E) (F : E → E) (R : ℝ), 0 < R ∧ fderiv ℝ r x w = 1 ∧ F 0 = x ∧
      HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 ∧
      (∀ y ∈ Metric.closedBall 0 R, ContDiffAt ℝ 3 F y) ∧
      (∀ y ∈ Metric.closedBall 0 R, flatteningMap r x (fderiv ℝ r x) w (F y) = y) ∧
      (∀ y ∈ Metric.closedBall 0 R, r (F y) - r x = fderiv ℝ r x y) := by
  have hsurj := OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top (fderiv ℝ r x) hg
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hsurj 1
  let P := flatteningMap r x (fderiv ℝ r x) w
  have hP : ContDiffAt ℝ 3 P x := (contDiff_flatteningMap hr x _ w).contDiffAt
  have hd : HasFDerivAt P (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x :=
    hasFDerivAt_flatteningMap (hr.differentiable (by norm_num) x).hasFDerivAt w
  let F := hP.localInverse hd (by norm_num)
  have hPx : P x = 0 := flatteningMap_base r x _ w
  have hF0 : F 0 = x := by rw [← hPx]; exact hP.localInverse_apply_image hd (by norm_num)
  have hF : ContDiffAt ℝ 3 F 0 := by
    rw [← hPx]; exact hP.to_localInverse hd (by norm_num)
  have hstrict := hP.hasStrictFDerivAt' hd (by norm_num)
  have hDF : HasFDerivAt F (ContinuousLinearMap.id ℝ E) 0 := by
    simpa [F, ContDiffAt.localInverse, hstrict, hPx] using hstrict.to_localInverse.hasFDerivAt
  have hinv : ∀ᶠ y in 𝓝 (0 : E), P (F y) = y := by
    simpa [F, ContDiffAt.localInverse, hstrict, hPx] using hstrict.eventually_right_inverse
  have hgood : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 3 F y ∧ P (F y) = y :=
    (hF.eventually (by norm_num)).and hinv
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hgood
  have hsmall : Metric.closedBall (0 : E) (ε / 2) ⊆ Metric.ball 0 ε :=
    Metric.closedBall_subset_ball (by linarith)
  refine ⟨w, F, ε / 2, by positivity, hw, hF0, hDF,
    (fun y hy => (heps (hsmall hy)).1), (fun y hy => (heps (hsmall hy)).2), ?_⟩
  intro y hy
  have he := congrArg (fderiv ℝ r x) (heps (hsmall hy)).2
  rwa [flatteningMap_level r x _ w hw] at he

end OAI.Analysis.PDE.Elliptic
