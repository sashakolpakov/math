import OAI.Analysis.PDE.Elliptic.Boundary.Correction

/-! The curvature term in the Hessian chain rule is Lipschitz using only
two derivatives of the solution and three derivatives of the fixed chart. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem operator_norm_le_of_inner_unit (A : E →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v w, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 → |inner ℝ (A v) w| ≤ C) : ‖A‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro v hv
  by_cases hz : A v = 0
  · simpa [hz] using hC
  have hp : 0 < ‖A v‖ := norm_pos_iff.mpr hz
  let w := ‖A v‖⁻¹ • A v
  have hw : ‖w‖ ≤ 1 := by simp [w, norm_smul, hp.ne']
  have hi : inner ℝ (A v) w = ‖A v‖ := by
    simp only [w, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  simpa only [hi, abs_of_nonneg (norm_nonneg _)] using h v w hv.le hw

def chartCurvature (u : E → ℝ) (G : E → E) (z : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient (fun y => fderiv ℝ u (G z) (G y))) z

theorem chartCurvature_inner {G : E → E} (hG : ContDiff ℝ 2 G)
    (u : E → ℝ) (z v w : E) :
    inner ℝ (chartCurvature u G z v) w =
      fderiv ℝ u (G z) (fderiv ℝ (fderiv ℝ G) z v w) := by
  have hL : ContDiff ℝ 2 (fun y => fderiv ℝ u (G z) (G y)) := (fderiv ℝ u (G z)).contDiff.comp hG
  rw [chartCurvature, inner_fderiv_gradient_at hL.contDiffAt,
    second_fderiv_linear_comp _ hG.contDiffAt]

theorem chartCurvature_difference {G : E → E} (hG : ContDiff ℝ 2 G)
    (u : E → ℝ) (z z' : E) :
    ‖chartCurvature u G z - chartCurvature u G z'‖ ≤
      ‖fderiv ℝ u (G z) - fderiv ℝ u (G z')‖ * ‖fderiv ℝ (fderiv ℝ G) z‖ +
      ‖fderiv ℝ u (G z')‖ * ‖fderiv ℝ (fderiv ℝ G) z - fderiv ℝ (fderiv ℝ G) z'‖ := by
  apply operator_norm_le_of_inner_unit _ (by positivity)
  intro v w hv hw
  simp only [sub_apply, inner_sub_left, chartCurvature_inner hG]
  let L := fderiv ℝ u (G z)
  let L' := fderiv ℝ u (G z')
  let B := fderiv ℝ (fderiv ℝ G) z
  let B' := fderiv ℝ (fderiv ℝ G) z'
  have hid : L (B v w) - L' (B' v w) = (L - L') (B v w) + L' ((B - B') v w) := by
    simp only [sub_apply, map_sub]
    ring
  change |L (B v w) - L' (B' v w)| ≤ _
  rw [hid]
  have hb : ‖B v w‖ ≤ ‖B‖ := by
    exact (B.le_opNorm₂ v w).trans (by nlinarith [norm_nonneg B, mul_le_mul hv hw (norm_nonneg _) zero_le_one])
  have hb' : ‖(B - B') v w‖ ≤ ‖B - B'‖ := by
    exact ((B - B').le_opNorm₂ v w).trans
      (by nlinarith [norm_nonneg (B - B'), mul_le_mul hv hw (norm_nonneg _) zero_le_one])
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact ((L - L').le_opNorm (B v w)).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  · exact (L'.le_opNorm ((B - B') v w)).trans (mul_le_mul_of_nonneg_left hb' (norm_nonneg _))

omit [FiniteDimensional ℝ E] in
theorem third_fderiv_norm_le_iterated {G : E → E} (z : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ G)) z‖ ≤ ‖iteratedFDeriv ℝ 3 G z‖ := by
  have h := second_fderiv_norm_le_iterated (g := fderiv ℝ G) z
  simpa only [norm_iteratedFDeriv_fderiv] using h

theorem chartCurvature_lipschitz {u : E → ℝ} {G : E → E} {S : Set E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S) (hV : 0 ≤ V)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ V)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    ‖chartCurvature u G z - chartCurvature u G z'‖ ≤ (V ^ 3 + V ^ 2) * ‖z - z'‖ := by
  have hDG : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hD2G : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ G)) := hDG.fderiv_right (by norm_num)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hda (y) : DifferentiableAt ℝ (fun y => fderiv ℝ u (G y)) y :=
    (hDu.differentiable (by norm_num) (G y)).comp y (hG.differentiable (by norm_num) y)
  have hba (y) (hy : y ∈ S) : ‖fderiv ℝ (fun y => fderiv ℝ u (G y)) y‖ ≤ V ^ 2 := by
    rw [show fderiv ℝ (fun y => fderiv ℝ u (G y)) y =
        (fderiv ℝ (fderiv ℝ u) (G y)).comp (fderiv ℝ G y) from
        ((hDu.differentiable (by norm_num) (G y)).hasFDerivAt.comp y
          (hG.differentiable (by norm_num) y).hasFDerivAt).fderiv]
    have hh := (fderiv ℝ (fderiv ℝ u) (G y)).opNorm_comp_le (fderiv ℝ G y)
    rw [← norm_fderiv_gradient hu] at hh
    exact hh.trans (by nlinarith [mul_le_mul (hu2 y hy) (hG1 y hy) (norm_nonneg _) hV])
  have ha := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y (_ : y ∈ S) => hda y) hba hS hz' hz
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ S) => hD2G.differentiable (by norm_num) y)
    (fun y hy => (third_fderiv_norm_le_iterated y).trans (hG3 y hy)) hS hz' hz
  apply (chartCurvature_difference (hG.of_le (by norm_num)) u z z').trans
  have h1 := mul_le_mul ha ((second_fderiv_norm_le_iterated z).trans (hG2 z hz))
    (norm_nonneg _) (by positivity : 0 ≤ V ^ 2 * ‖z - z'‖)
  have h2 := mul_le_mul (hu1 z' hz') hb (norm_nonneg _) hV
  nlinarith

theorem hessianOperator_lipschitz {f : E → ℝ} {S : Set E} {V : ℝ}
    (hf : ContDiff ℝ 3 f) (hS : Convex ℝ S)
    (h3 : ∀ x ∈ S, ‖iteratedFDeriv ℝ 3 f x‖ ≤ V)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ V * ‖x - y‖ := by
  have hDf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD2f : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hDf.fderiv_right (by norm_num)
  have hbound (z) (hz : z ∈ S) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ V := by
    have hh := second_fderiv_norm_le_iterated (g := fderiv ℝ f) z
    have hh' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) z‖ ≤ ‖iteratedFDeriv ℝ 3 f z‖ := by
      simpa only [norm_iteratedFDeriv_fderiv] using hh
    exact hh'.trans (h3 z hz)
  have hd := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => hD2f.differentiable (by norm_num) z) hbound hS hy hx
  apply le_trans _ hd
  apply operator_norm_le_of_inner_unit _ (norm_nonneg _)
  intro v w hv hw
  simp only [sub_apply, inner_sub_left,
    inner_fderiv_gradient_at (hf.of_le (by norm_num)).contDiffAt]
  change ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) v w‖ ≤ _
  apply (ContinuousLinearMap.le_opNorm₂ _ v w).trans
  nlinarith [norm_nonneg (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y),
    mul_le_mul hv hw (norm_nonneg _) zero_le_one]

end OAI.Analysis.PDE.Elliptic
