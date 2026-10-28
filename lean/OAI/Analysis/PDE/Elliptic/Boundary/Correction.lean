import OAI.Analysis.PDE.Elliptic.Boundary.LogFieldHolder
import OAI.Analysis.PDE.Elliptic.HessianNorm

/-! The lower-order term in a tangent-field normal derivative is genuinely
Lipschitz under the already available C² bounds. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

section Norms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv_clm_apply_norm_le {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y (g y)) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  rw [fderiv_clm_apply hf hg]
  exact (norm_add_le _ _).trans (add_le_add ((f x).opNorm_comp_le _)
    (by simpa only [ContinuousLinearMap.opNorm_flip] using (fderiv ℝ f x).flip.le_opNorm (g x)))

theorem second_fderiv_norm_le_iterated {g : E → F} (x : E) :
    ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ ‖iteratedFDeriv ℝ 2 g x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _)
  intro v w
  have hh := (iteratedFDeriv ℝ 2 g x).le_opNorm ![v, w]
  simpa [iteratedFDeriv_two_apply, Fin.prod_univ_two, mul_assoc] using hh

end Norms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def fieldNormalCorrection (u : E → ℝ) (T F : E → E) (v z : E) : ℝ :=
  fderiv ℝ u (F z) (fderiv ℝ T (F z) (fderiv ℝ F z v))

theorem fieldNormalCorrection_derivative_bound
    {u : E → ℝ} {T F : E → E} {v z : E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hT : ContDiff ℝ 2 T) (hF : ContDiffAt ℝ 2 F z)
    (hV : 0 ≤ V) (hv : ‖v‖ ≤ 1)
    (hu1 : ‖fderiv ℝ u (F z)‖ ≤ V) (hu2 : ‖fderiv ℝ (gradient u) (F z)‖ ≤ V)
    (hT1 : ‖fderiv ℝ T (F z)‖ ≤ V) (hT2 : ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V)
    (hF1 : ‖fderiv ℝ F z‖ ≤ V) (hF2 : ‖iteratedFDeriv ℝ 2 F z‖ ≤ V) :
    DifferentiableAt ℝ (fieldNormalCorrection u T F v) z ∧
    ‖fderiv ℝ (fieldNormalCorrection u T F v) z‖ ≤ V ^ 3 + 2 * V ^ 4 := by
  let a := fun y => fderiv ℝ u (F y)
  let b := fun y => fderiv ℝ T (F y)
  let c := fun y => fderiv ℝ F y v
  have hFd := hF.differentiableAt (by norm_num)
  have hau := (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (F z)
  have hbT := (hT.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) (F z)
  have hcF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have ha : DifferentiableAt ℝ a z := hau.comp z hFd
  have hb : DifferentiableAt ℝ b z := hbT.comp z hFd
  have hc : DifferentiableAt ℝ c z := hcF.clm_apply (differentiableAt_const v)
  have hbc : DifferentiableAt ℝ (fun y => b y (c y)) z := hb.clm_apply hc
  have habc : DifferentiableAt ℝ (fieldNormalCorrection u T F v) z := ha.clm_apply hbc
  refine ⟨habc, ?_⟩
  have hDa : ‖fderiv ℝ a z‖ ≤ V ^ 2 := by
    rw [show fderiv ℝ a z = (fderiv ℝ (fderiv ℝ u) (F z)).comp (fderiv ℝ F z) from
      (hau.hasFDerivAt.comp z hFd.hasFDerivAt).fderiv]
    have he := norm_fderiv_gradient hu (F z)
    have hh := (fderiv ℝ (fderiv ℝ u) (F z)).opNorm_comp_le (fderiv ℝ F z)
    rw [← he] at hh
    exact hh.trans (by nlinarith [mul_le_mul hu2 hF1 (norm_nonneg _) hV])
  have hDb : ‖fderiv ℝ b z‖ ≤ V ^ 2 := by
    rw [show fderiv ℝ b z = (fderiv ℝ (fderiv ℝ T) (F z)).comp (fderiv ℝ F z) from
      (hbT.hasFDerivAt.comp z hFd.hasFDerivAt).fderiv]
    have hm := mul_le_mul ((second_fderiv_norm_le_iterated (F z)).trans hT2) hF1 (norm_nonneg _) hV
    exact ((fderiv ℝ (fderiv ℝ T) (F z)).opNorm_comp_le _).trans (by nlinarith)
  have hcz : ‖c z‖ ≤ V := by
    exact ((fderiv ℝ F z).le_opNorm v).trans (by nlinarith [mul_le_mul hF1 hv (norm_nonneg _) hV])
  have hDc : ‖fderiv ℝ c z‖ ≤ V := by
    have hh := fderiv_clm_apply_norm_le hcF (differentiableAt_const v)
    have hz : fderiv ℝ (fun _ : E => v) z = 0 := by simp
    rw [hz, norm_zero, mul_zero, zero_add] at hh
    have hm := mul_le_mul ((second_fderiv_norm_le_iterated z).trans hF2) hv (norm_nonneg _) hV
    exact hh.trans (by nlinarith)
  have hbcz : ‖b z (c z)‖ ≤ V ^ 2 :=
    ((fderiv ℝ T (F z)).le_opNorm (c z)).trans (by nlinarith [mul_le_mul hT1 hcz (norm_nonneg _) hV])
  have hDbc : ‖fderiv ℝ (fun y => b y (c y)) z‖ ≤ V ^ 2 + V ^ 3 := by
    apply (fderiv_clm_apply_norm_le hb hc).trans
    have h1 := mul_le_mul hT1 hDc (norm_nonneg _) hV
    have h2 := mul_le_mul hDb hcz (norm_nonneg _) (sq_nonneg V)
    dsimp only [b] at *
    nlinarith
  apply (fderiv_clm_apply_norm_le ha hbc).trans
  have h1 := mul_le_mul hu1 hDbc (norm_nonneg _) hV
  have h2 := mul_le_mul hDa hbcz (norm_nonneg _) (sq_nonneg V)
  dsimp only [a] at *
  nlinarith

theorem fieldNormalCorrection_lipschitz
    {u : E → ℝ} {T F : E → E} {v : E} {V : ℝ} {S : Set E}
    (hu : ContDiff ℝ 2 u) (hT : ContDiff ℝ 2 T) (hS : Convex ℝ S)
    (hF : ∀ z ∈ S, ContDiffAt ℝ 2 F z) (hV : 0 ≤ V) (hv : ‖v‖ ≤ 1)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (F z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (F z)‖ ≤ V)
    (hT1 : ∀ z ∈ S, ‖fderiv ℝ T (F z)‖ ≤ V)
    (hT2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V)
    (hF1 : ∀ z ∈ S, ‖fderiv ℝ F z‖ ≤ V)
    (hF2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 F z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    |fieldNormalCorrection u T F v z - fieldNormalCorrection u T F v z'| ≤
      (V ^ 3 + 2 * V ^ 4) * ‖z - z'‖ := by
  have hb (y) (hy : y ∈ S) := fieldNormalCorrection_derivative_bound hu hT (hF y hy)
    hV hv (hu1 y hy) (hu2 y hy) (hT1 y hy) (hT2 y hy) (hF1 y hy) (hF2 y hy)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => (hb y hy).1)
    (fun y hy => (hb y hy).2) hS hz' hz

end OAI.Analysis.PDE.Elliptic
