import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PotentialDerivatives

/-! Smooth regularizations of the Newtonian kernel and their actual Hessians. -/

noncomputable section
open scoped RealInnerProductSpace Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def shiftedRadialPower (p s : ℝ) (x : E) : ℝ := (s + ‖x‖ ^ 2) ^ p

def shiftedRadialGradient (p s : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)) • innerSL ℝ x

def shiftedRadialHessian (p s : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 * p * (s + ‖x‖ ^ 2) ^ (p - 1)) • realInnerBilinear +
    (4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2)) •
      (innerSL ℝ x).smulRight (innerSL ℝ x)

theorem contDiff_shiftedRadialPower (p : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ⊤ (shiftedRadialPower (E := E) p s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).contDiffAt).rpow_const_of_ne
    (ne_of_gt (add_pos_of_pos_of_nonneg hs (sq_nonneg ‖x‖)))

theorem hasFDerivAt_shiftedRadialPower (p : ℝ) {s : ℝ} (hs : 0 < s) (x : E) :
    HasFDerivAt (shiftedRadialPower p s) (shiftedRadialGradient p s x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add s).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg hs (sq_nonneg ‖x‖))))
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at h
  have hc : (p * (s + ‖x‖ ^ 2) ^ (p - 1)) * 2 = 2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) := by ring
  simpa only [shiftedRadialPower, shiftedRadialGradient, smul_smul, Nat.cast_ofNat, hc] using! h

theorem shiftedRadialHessian_apply (p s : ℝ) (x v w : E) :
    shiftedRadialHessian p s x v w =
      2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2) * ⟪x, v⟫ * ⟪x, w⟫ := by
  simp [shiftedRadialHessian, smul_eq_mul, mul_assoc]

theorem hasFDerivAt_shiftedRadialGradient (p : ℝ) {s : ℝ} (hs : 0 < s) (x : E) :
    HasFDerivAt (shiftedRadialGradient p s) (shiftedRadialHessian p s x) x := by
  have hp := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add s).rpow_const
    (p := p - 1) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg hs (sq_nonneg ‖x‖))))
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hp
  have h := (hp.const_mul (2 * p)).smul (realInnerBilinear (E := E)).hasFDerivAt
  convert! h using 1
  ext v w
  change 2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      4 * p * (p - 1) * (s + ‖x‖ ^ 2) ^ (p - 2) * (⟪x, v⟫ * ⟪x, w⟫) =
    2 * p * (s + ‖x‖ ^ 2) ^ (p - 1) * ⟪v, w⟫ +
      (2 * p * (((p - 1) * (s + ‖x‖ ^ 2) ^ (p - 1 - 1) * 2) * ⟪x, v⟫)) * ⟪x, w⟫
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem fderiv_shiftedRadialPower (p : ℝ) {s : ℝ} (hs : 0 < s) (x : E) :
    fderiv ℝ (shiftedRadialPower p s) x = shiftedRadialGradient p s x :=
  (hasFDerivAt_shiftedRadialPower p hs x).fderiv

theorem second_fderiv_shiftedRadialPower (p : ℝ) {s : ℝ} (hs : 0 < s) (x : E) :
    fderiv ℝ (fderiv ℝ (shiftedRadialPower p s)) x = shiftedRadialHessian p s x := by
  have he : fderiv ℝ (shiftedRadialPower (E := E) p s) = shiftedRadialGradient p s :=
    funext (fderiv_shiftedRadialPower p hs)
  rw [he]
  exact (hasFDerivAt_shiftedRadialGradient p hs x).fderiv

end OAI.Analysis.PDE.Schauder
