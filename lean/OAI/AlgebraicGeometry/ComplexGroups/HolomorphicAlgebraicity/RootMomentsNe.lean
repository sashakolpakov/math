import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Root Moments Ne -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootMomentsNe.Constructions.RootMoments

noncomputable section

/-!
# Contour formulas for finite root multisets

Power sums of roots, including repeated roots, are contour integrals of the
logarithmic derivative. These formulas are used to construct coefficients in
analytic elimination.
-/

open Set _root_.Metric _root_.Complex
open scoped BigOperators Real

def rootProduct {d : ℕ} (roots : Fin d → ℂ) (z : ℂ) : ℂ := ∏ i, (z - roots i)

theorem logDeriv_rootProduct {d : ℕ} (roots : Fin d → ℂ) (z : ℂ)
    (hz : ∀ i, z ≠ roots i) :
    logDeriv (rootProduct roots) z = ∑ i, (z - roots i)⁻¹ := by
  change logDeriv (fun w : ℂ => ∏ i, (w - roots i)) z = _
  have hprod : (fun w : ℂ => ∏ i, (w - roots i)) = ∏ i, (fun w : ℂ => w - roots i) := by
    funext w
    simp only [Finset.prod_apply]
  rw [hprod, logDeriv_prod (fun i _ => sub_ne_zero.mpr (hz i))
    (fun _ _ => differentiableAt_id.sub_const _)]
  apply Finset.sum_congr rfl
  intro i _
  simp [logDeriv]

theorem ne_root_on_circle {d : ℕ} (roots : Fin d → ℂ) {c : ℂ} {R : ℝ}
    (hroots : ∀ i, roots i ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) (i : Fin d) :
    z ≠ roots i := by
  intro h
  rw [h] at hz
  exact (ne_of_lt (mem_ball.mp (hroots i))) (mem_sphere.mp hz)

/-- Cauchy's formula computes each weighted simple-pole term. -/
theorem root_kernel_integral {c a : ℂ} {R : ℝ} (ha : a ∈ ball c R) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * (z - a)⁻¹) = (2 * Real.pi * Complex.I) * a ^ k := by
  have hpower : Differentiable ℂ (fun z : ℂ => z ^ k) := differentiable_id.pow k
  have h := hpower.differentiableOn.circleIntegral_sub_inv_smul ha
  simpa only [smul_eq_mul, mul_comm] using h

/-- A root product's logarithmic derivative recovers every root power sum. -/
theorem integral_rootProduct_moment {d : ℕ} (roots : Fin d → ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hroots : ∀ i, roots i ∈ ball c R) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * logDeriv (rootProduct roots) z) =
      (2 * Real.pi * Complex.I) * ∑ i, (roots i) ^ k := by
  have hcongr : (∮ z in C(c, R), z ^ k * logDeriv (rootProduct roots) z) =
      ∮ z in C(c, R), ∑ i, z ^ k * (z - roots i)⁻¹ := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp only
    rw [logDeriv_rootProduct roots z (ne_root_on_circle roots hroots hz), Finset.mul_sum]
  rw [hcongr, circleIntegral.integral_fun_sum]
  · simp only [root_kernel_integral (hroots _), Finset.mul_sum]
  · intro i _
    apply ContinuousOn.circleIntegrable hR.le
    apply (continuousOn_id.pow k).mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    exact sub_ne_zero.mpr (ne_root_on_circle roots hroots hz i)

theorem circleIntegrable_rootProduct_moment {d : ℕ} (roots : Fin d → ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hroots : ∀ i, roots i ∈ ball c R) (k : ℕ) :
    CircleIntegrable (fun z => z ^ k * logDeriv (rootProduct roots) z) c R := by
  have hc : ContinuousOn (fun z => ∑ i, z ^ k * (z - roots i)⁻¹) (sphere c R) := by
    apply continuousOn_finsetSum
    intro i _
    apply (continuousOn_id.pow k).mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    exact sub_ne_zero.mpr (ne_root_on_circle roots hroots hz i)
  apply ContinuousOn.circleIntegrable hR.le
  apply hc.congr
  intro z hz
  dsimp only
  rw [logDeriv_rootProduct roots z (ne_root_on_circle roots hroots hz), Finset.mul_sum]

/-- A holomorphic factor with no zeros contributes no root moments. -/
theorem integral_nonvanishing_moment {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hgn : ∀ z ∈ closedBall c R, g z ≠ 0) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * logDeriv g z) = 0 := by
  have hlog : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) := hg.deriv.div hg hgn
  have hpow : Differentiable ℂ (fun z : ℂ => z ^ k) := differentiable_id.pow k
  have hdiff := hpow.differentiableOn.fun_mul hlog.differentiableOn
  exact (hdiff.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR

/-- Multiplication by an analytic unit leaves all contour root moments
unchanged. This allows moments to be read from local zero factorizations. -/
theorem integral_rootProduct_mul_nonvanishing {d : ℕ} (roots : Fin d → ℂ)
    {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hroots : ∀ i, roots i ∈ ball c R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hgn : ∀ z ∈ closedBall c R, g z ≠ 0) (k : ℕ) :
    (∮ z in C(c, R), z ^ k * logDeriv (fun w => rootProduct roots w * g w) z) =
      (2 * Real.pi * Complex.I) * ∑ i, (roots i) ^ k := by
  have hP : Differentiable ℂ (rootProduct roots) := by
    unfold rootProduct
    fun_prop
  have hlog : AnalyticOnNhd ℂ (logDeriv g) (closedBall c R) := hg.deriv.div hg hgn
  have hunit : CircleIntegrable (fun z => z ^ k * logDeriv g z) c R :=
    ((continuousOn_id.pow k).mul
      (hlog.continuousOn.mono sphere_subset_closedBall)).circleIntegrable hR.le
  have heq : (∮ z in C(c, R), z ^ k * logDeriv (fun w => rootProduct roots w * g w) z) =
      ∮ z in C(c, R), z ^ k * logDeriv (rootProduct roots) z + z ^ k * logDeriv g z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz' : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hpz : rootProduct roots z ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact sub_ne_zero.mpr (ne_root_on_circle roots hroots hz i)
    dsimp only
    change z ^ k * logDeriv (rootProduct roots * g) z = _
    rw [logDeriv_mul z hpz (hgn z hz') (hP z) ((hg z hz').differentiableAt), mul_add]
  rw [heq, circleIntegral.integral_add (circleIntegrable_rootProduct_moment roots hR hroots k) hunit,
    integral_nonvanishing_moment hR.le hg hgn, add_zero]
  exact integral_rootProduct_moment roots hR hroots k

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootMomentsNe.Constructions.RootMoments
