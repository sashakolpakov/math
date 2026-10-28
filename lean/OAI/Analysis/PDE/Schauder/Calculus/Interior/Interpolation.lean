import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Interpolation
import OAI.Analysis.PDE.Nonlinear.Dilation
import OAI.Analysis.PDE.Schauder.Dirichlet.HalfspaceLowerJets

/-! Quantitative full-space lower-jet interpolation, with arbitrary absorption. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

theorem fullspace_gradient_bound {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) {D M : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hH : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ D)
    (hbound : ∀ x, |u x| ≤ M) :
    ∀ x, ‖fderiv ℝ u x‖ ≤ (m : ℝ) * (D + 2*M) := by
  intro x
  let v := fun z => u (x+z)
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_const.add contDiff_id)
  have hsecond (z) : fderiv ℝ (fderiv ℝ v) z = fderiv ℝ (fderiv ℝ u) (x+z) := by
    ext a b
    exact second_fderiv_comp_affine u hu (ContinuousLinearMap.id ℝ _) x z a b
  have hfirst : fderiv ℝ v 0 = fderiv ℝ u x := by
    have ht := OAI.Analysis.PDE.Nonlinear.fderiv_linearAffine u (hu.differentiable (by norm_num)) x 0
      (ContinuousLinearMap.id ℝ _)
    simpa only [ContinuousLinearMap.id_apply, add_zero, ContinuousLinearMap.comp_id] using ht
  have hb := halfspace_gradient_bound k hv hD hM
    (fun z _ => by rw [hsecond]; exact hH (x+z)) (fun z _ => hbound (x+z)) 0 (by simp)
  rwa [hfirst] at hb

theorem fullspace_lower_jet_interpolation {m : ℕ} (k : Fin m) {α ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) :
    ∃ B > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
      ∀ H M, 0 ≤ H → 0 ≤ M → (∀ x, |u x| ≤ M) →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖^α) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*H+B*M) ∧
      (∀ x, ‖fderiv ℝ u x‖ ≤ ε*H+B*M) ∧
      (∀ x y, |u x-u y| ≤ (ε*H+B*M)*‖x-y‖^α) ∧
      (∀ x y, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ (ε*H+B*M)*‖x-y‖^α) := by
  let c : ℝ := 1+2*m
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨B₀, hB₀, hinterp⟩ := hessian_interpolation (m := m) hα (div_pos hε hc)
  let B : ℝ := c*B₀+4*m+3
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro u hu huc H M hH hM hbound hh
  let D := (ε/c)*H+B₀*M
  let G : ℝ := m*(D+2*M)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hHess : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ D := hinterp u hu huc H M hH hM hbound hh
  have hGrad : ∀ x, ‖fderiv ℝ u x‖ ≤ G := fullspace_gradient_bound k u hu hD hM hHess hbound
  have hcore : c*D = ε*H+c*B₀*M := by dsimp only [D]; field_simp
  have hc1 : 1 ≤ c := by dsimp only [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hmc : (m : ℝ) ≤ c := by dsimp only [c]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hDle : D ≤ ε*H+B*M := by
    have hm := mul_le_mul_of_nonneg_right hc1 hD
    dsimp only [B]
    nlinarith
  have hGle : G ≤ ε*H+B*M := by
    have hm := mul_le_mul_of_nonneg_right hmc hD
    dsimp only [G, B]
    nlinarith
  have hFU : G+2*M ≤ ε*H+B*M := by
    have hm := mul_le_mul_of_nonneg_right hmc hD
    dsimp only [G, B]
    nlinarith
  have hDG : D+2*G ≤ ε*H+B*M := by
    have he : D+2*G = c*D+4*m*M := by dsimp only [G, c]; ring
    rw [he, hcore]
    dsimp only [B]
    nlinarith
  have hLipU (x y) : ‖u x-u y‖ ≤ G*‖x-y‖ :=
    (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin m)))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hu.differentiable (by norm_num) z) (fun z _ => hGrad z) (mem_univ y) (mem_univ x)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hLipD (x y) : ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ D*‖x-y‖ :=
    (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin m)))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hDu.differentiable one_ne_zero z) (fun z _ => hHess z) (mem_univ y) (mem_univ x)
  have hHolderU := holder_of_bounded_lipschitz u hα.le hα1 hM hG
    (fun z => by simpa only [Real.norm_eq_abs] using hbound z) hLipU
  have hHolderD := holder_of_bounded_lipschitz (fderiv ℝ u) hα.le hα1 hG hD hGrad hLipD
  refine ⟨fun x => (hHess x).trans hDle, fun x => (hGrad x).trans hGle, ?_, ?_⟩
  · intro x y
    simpa only [Real.norm_eq_abs] using (hHolderU x y).trans
      (mul_le_mul_of_nonneg_right hFU (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x y
    exact (hHolderD x y).trans (mul_le_mul_of_nonneg_right hDG (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
