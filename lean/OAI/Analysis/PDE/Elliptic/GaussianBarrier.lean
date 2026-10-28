import OAI.Analysis.PDE.Elliptic.Gaussian
import OAI.Analysis.PDE.Elliptic.LinearCalculus

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def gaussianBarrier (a R : ℝ) (x : E) : ℝ := Real.exp (-a * R ^ 2) - radialGaussian a x

omit [FiniteDimensional ℝ E] in
theorem gaussianBarrier_contDiff (a R : ℝ) :
    ContDiff ℝ ⊤ (gaussianBarrier (E := E) a R) :=
  contDiff_const.sub (radialGaussian_contDiff a)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem gaussianBarrier_zero (a R : ℝ) {x : E} (hx : ‖x‖ = R) :
    gaussianBarrier a R x = 0 := by simp [gaussianBarrier, radialGaussian, hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem radialGaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : E) :
    radialGaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem gaussianBarrier_lower {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (x : E) :
    -1 ≤ gaussianBarrier a R x := by
  have h := radialGaussian_le_one ha x
  have hpos := Real.exp_pos (-a * R ^ 2)
  dsimp [gaussianBarrier]
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A fixed strictly negative gap on every strictly smaller ball. -/
theorem gaussianBarrier_inner_gap {a r R : ℝ} (ha : 0 < a)
    (hr : 0 ≤ r) (hrR : r < R) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ x : E, ‖x‖ ≤ r → gaussianBarrier a R x ≤ -eta := by
  refine ⟨Real.exp (-a * r ^ 2) - Real.exp (-a * R ^ 2), ?_, ?_⟩
  · apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    have hs : r ^ 2 < R ^ 2 := by nlinarith
    nlinarith
  · intro x hx
    have hs : ‖x‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg x]
    have he : Real.exp (-a * r ^ 2) ≤ radialGaussian a x := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [gaussianBarrier]
    linarith

theorem ellipticTrace_gaussianBarrier (A : E → E →L[ℝ] E) (a R : ℝ) (x : E) :
    ellipticTrace A (gaussianBarrier a R) x =
      2 * a * radialGaussian a x *
        (LinearMap.trace ℝ E (A x).toLinearMap - 2 * a * inner ℝ x (A x x)) := by
  change ellipticTrace A (fun y ↦ Real.exp (-a * R ^ 2) - radialGaussian a y) x = _
  rw [ellipticTrace_const_sub A ((radialGaussian_contDiff a).of_le (by simp)),
    ellipticTrace_radialGaussian]
  ring

/-- With `a` chosen from the ellipticity constants, the barrier is an
elliptic supersolution outside the chosen inner ball. -/
theorem ellipticTrace_gaussianBarrier_nonpos
    (A : E → E →L[ℝ] E) {a lam L r : ℝ} (R : ℝ) (ha : 0 ≤ a) (hlam : 0 ≤ lam)
    (hscale : L * Module.finrank ℝ E ≤ 2 * a * lam * r ^ 2)
    (x : E) (hx : r ^ 2 ≤ ‖x‖ ^ 2)
    (hlo : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hhi : ∀ v : E, inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) :
    ellipticTrace A (gaussianBarrier a R) x ≤ 0 := by
  rw [ellipticTrace_gaussianBarrier]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (by positivity) (radialGaussian_pos a x).le
  · have htr := trace_le_of_quadratic_upper (A x) hhi
    have hq := mul_le_mul_of_nonneg_left (hlo x) (show 0 ≤ 2 * a by positivity)
    have hr := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * a * lam by positivity)
    nlinarith

/-- The positive part of the barrier forcing is uniformly bounded, using
only the two ellipticity constants and the ambient dimension. -/
theorem ellipticTrace_gaussianBarrier_upper
    (A : E → E →L[ℝ] E) {a lam L : ℝ} (R : ℝ) (ha : 0 ≤ a) (hlam : 0 ≤ lam)
    (hL : 0 ≤ L) (x : E)
    (hlo : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hhi : ∀ v : E, inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) :
    ellipticTrace A (gaussianBarrier a R) x ≤ 2 * a * (L * Module.finrank ℝ E) := by
  rw [ellipticTrace_gaussianBarrier]
  have htr := trace_le_of_quadratic_upper (A x) hhi
  have hq : 0 ≤ inner ℝ x (A x x) :=
    (mul_nonneg hlam (sq_nonneg _)).trans (hlo x)
  have hterm : LinearMap.trace ℝ E (A x).toLinearMap - 2 * a * inner ℝ x (A x x) ≤
      L * Module.finrank ℝ E := by nlinarith
  calc
    _ ≤ (2 * a * radialGaussian a x) * (L * Module.finrank ℝ E) :=
      mul_le_mul_of_nonneg_left hterm
        (mul_nonneg (by positivity) (radialGaussian_pos a x).le)
    _ ≤ _ := by
      have hg := mul_le_mul_of_nonneg_left (radialGaussian_le_one ha x)
        (show 0 ≤ (2 * a) * (L * (Module.finrank ℝ E : ℝ)) by positivity)
      nlinarith only [hg]

end OAI.Analysis.PDE.Elliptic
