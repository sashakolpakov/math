import OAI.Analysis.PDE.Elliptic.Boundary.Comparison
import OAI.Analysis.PDE.Elliptic.GaussianBarrier

/-! A quantitative Hopf barrier with an explicit bounded-forcing correction.
This is a real elliptic comparison argument, valid for variable coefficients. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def hopfBarrier (a R l k : ℝ) (x : E) : ℝ :=
  (-l) • gaussianBarrier a R x + (-k) • quadraticBarrier 0 R x

omit [FiniteDimensional ℝ E] in
theorem hopfBarrier_contDiff (a R l k : ℝ) : ContDiff ℝ 2 (hopfBarrier (E := E) a R l k) :=
  ((gaussianBarrier_contDiff a R).of_le (by simp)).const_smul (-l) |>.add
    (((quadraticBarrier_contDiff 0 R).of_le (by simp)).const_smul (-k))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hopfBarrier_zero (a R l k : ℝ) {x : E} (hx : ‖x‖ = R) :
    hopfBarrier a R l k x = 0 := by
  simp [hopfBarrier, gaussianBarrier_zero a R hx, quadraticBarrier, hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hopfBarrier_le_level {a R l k : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hl : 0 ≤ l) (hk : 0 ≤ k) {x : E} (hx : ‖x‖ ≤ R) : hopfBarrier a R l k x ≤ l := by
  have hg := mul_le_mul_of_nonneg_left (gaussianBarrier_lower ha R x) hl
  have hq := mul_nonneg hk (quadraticBarrier_nonneg hR
    (show x ∈ Metric.closedBall (0 : E) R by simpa using hx))
  dsimp only [hopfBarrier, smul_eq_mul]
  linarith

theorem ellipticTrace_hopfBarrier (A : E → E →L[ℝ] E) (a R l k : ℝ) (x : E) :
    ellipticTrace A (hopfBarrier a R l k) x =
      -l * ellipticTrace A (gaussianBarrier a R) x +
        2 * k * LinearMap.trace ℝ E (A x).toLinearMap := by
  unfold hopfBarrier
  rw [ellipticTrace_add_smul A
    (((gaussianBarrier_contDiff a R).of_le (by simp)).const_smul (-l))
    ((quadraticBarrier_contDiff 0 R).of_le (by simp)),
    ellipticTrace_smul A ((gaussianBarrier_contDiff a R).of_le (by simp)),
    ellipticTrace_quadraticBarrier]
  ring

theorem hopfBarrier_subsolution (A : E → E →L[ℝ] E)
    {a R l k lam L r : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (hscale : L * Module.finrank ℝ E ≤ 2 * a * lam * r ^ 2)
    (x : E) (hx : r ^ 2 ≤ ‖x‖ ^ 2)
    (hlo : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hhi : ∀ v : E, inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2) :
    2 * k * lam * Module.finrank ℝ E ≤ ellipticTrace A (hopfBarrier a R l k) x := by
  rw [ellipticTrace_hopfBarrier]
  have hg := ellipticTrace_gaussianBarrier_nonpos A R ha hlam hscale x hx hlo hhi
  have ht := mul_le_mul_of_nonneg_left (trace_ge_of_quadratic_lower (A x) hlo)
    (show 0 ≤ 2 * k by positivity)
  have hp : 0 ≤ -l * ellipticTrace A (gaussianBarrier a R) x := mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr hl) hg
  nlinarith only [ht, hp]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hopfBarrier_gap_lower {a R l k : ℝ} (hl : 0 ≤ l) (x : E) :
    (l * a * Real.exp (-a * R ^ 2) - k) * (R ^ 2 - ‖x‖ ^ 2) ≤ hopfBarrier a R l k x := by
  have he : Real.exp (-a * ‖x‖ ^ 2) =
      Real.exp (-a * R ^ 2) * Real.exp (a * (R ^ 2 - ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a * (R ^ 2 - ‖x‖ ^ 2)))
    (Real.exp_pos (-a * R ^ 2)).le
  rw [← he] at hh
  have hlh := mul_le_mul_of_nonneg_left hh hl
  dsimp only [hopfBarrier, gaussianBarrier, radialGaussian, quadraticBarrier, smul_eq_mul]
  simp only [sub_zero]
  nlinarith only [hlh]

omit [FiniteDimensional ℝ E] in
theorem hopfBarrier_normal_lower {a R l k : ℝ} (ha : 0 ≤ a) (hl : 0 ≤ l) (hk : 0 ≤ k)
    (v : E) (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    (l * a * R * Real.exp (-a * R ^ 2) - 2 * k * R) * t ≤
      hopfBarrier a R l k ((t - R) • v) := by
  have hn : ‖(t - R) • v‖ ^ 2 = (R - t) ^ 2 := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, sq_abs]
    ring
  have hg := hopfBarrier_gap_lower (a := a) (R := R) (k := k) hl ((t - R) • v)
  rw [hn] at hg
  have hc : 0 ≤ l * a * Real.exp (-a * R ^ 2) := by positivity
  have hgaplo : R * t ≤ R ^ 2 - (R - t) ^ 2 := by nlinarith
  have hgaphi : R ^ 2 - (R - t) ^ 2 ≤ 2 * R * t := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hgaplo hc
  have hq := mul_le_mul_of_nonneg_left hgaphi hk
  nlinarith only [hg, hp, hq]

theorem gaussian_hopf_annulus [Nontrivial E]
    (A : E → E →L[ℝ] E) {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {a R r l k lam L : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hrR : r < R)
    (hl : 0 ≤ l) (hk : 0 ≤ k) (hlam : 0 < lam)
    (hscale : L * Module.finrank ℝ E ≤ 2 * a * lam * r ^ 2)
    (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ R → ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hhi : ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ R → ∀ v : E, inner ℝ v (A x v) ≤ L * ‖v‖ ^ 2)
    (hLu : ∀ x, r ≤ ‖x‖ → ‖x‖ < R → ellipticTrace A u x ≤ 2 * k * lam * Module.finrank ℝ E)
    (hinner : ∀ x, ‖x‖ = r → l ≤ u x) (houter : ∀ x, ‖x‖ = R → 0 ≤ u x) :
    ∀ x, r ≤ ‖x‖ → ‖x‖ ≤ R → hopfBarrier a R l k x ≤ u x := by
  let K : Set E := {x | r ≤ ‖x‖} ∩ Metric.closedBall 0 R
  have hK : IsCompact K := by
    simpa only [K, inter_comm] using (isCompact_closedBall (0 : E) R).inter_right
      (isClosed_le (f := fun _ : E => r) continuous_const continuous_norm)
  have hmem (x : E) : x ∈ K ↔ r ≤ ‖x‖ ∧ ‖x‖ ≤ R := by simp [K]
  have hi (x : E) (hx : x ∈ interior K) : ‖x‖ < R := by
    have hiBall : x ∈ interior (Metric.closedBall (0 : E) R) :=
      interior_mono (show K ⊆ Metric.closedBall 0 R from inter_subset_right) hx
    simpa only [interior_closedBall', Metric.mem_ball, dist_zero_right] using hiBall
  have hcompare := ellipticTrace_comparison A hK (hopfBarrier_contDiff a R l k) hu
    (fun x hx v => (mul_nonneg hlam.le (sq_nonneg ‖v‖)).trans
      (hlo x ((hmem x).mp (interior_subset hx)).1 ((hmem x).mp (interior_subset hx)).2 v))
    (fun x hx => (mul_pos hlam (by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E))).trans_le
      (trace_ge_of_quadratic_lower (A x)
        (hlo x ((hmem x).mp (interior_subset hx)).1 ((hmem x).mp (interior_subset hx)).2)))
    (fun x hx => (hLu x ((hmem x).mp (interior_subset hx)).1 (hi x hx)).trans
      (hopfBarrier_subsolution A ha hl hk hlam.le hscale x
        (by nlinarith [(hmem x).mp (interior_subset hx)])
        (hlo x ((hmem x).mp (interior_subset hx)).1 ((hmem x).mp (interior_subset hx)).2)
        (hhi x ((hmem x).mp (interior_subset hx)).1 ((hmem x).mp (interior_subset hx)).2)))
    (fun x hx hxi => ?_)
  · intro x hrx hxR
    exact hcompare x ((hmem x).mpr ⟨hrx, hxR⟩)
  · have hx' := (hmem x).mp hx
    by_cases hxr : ‖x‖ = r
    · exact (hopfBarrier_le_level ha (hr.trans hrR.le) hl hk hx'.2).trans (hinner x hxr)
    by_cases hxR : ‖x‖ = R
    · rw [hopfBarrier_zero a R l k hxR]
      exact houter x hxR
    apply False.elim ∘ hxi
    have hU : IsOpen {y : E | r < ‖y‖ ∧ ‖y‖ < R} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hU.mem_nhds
      (show r < ‖x‖ ∧ ‖x‖ < R from ⟨lt_of_le_of_ne hx'.1 (Ne.symm hxr), lt_of_le_of_ne hx'.2 hxR⟩))
    intro y hy
    exact (hmem y).mpr ⟨hy.1.le, hy.2.le⟩

end OAI.Analysis.PDE.Elliptic
