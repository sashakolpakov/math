import OAI.Analysis.PDE.Elliptic.Boundary.GaussianHopf

/-! Propagation of a positive interior lower bound to the flat boundary.
The translated annuli and their containment are proved explicitly. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def closedHalfBall (v : E) : Set E := {x | ‖x‖ ≤ 1 ∧ 0 ≤ inner ℝ v x}
def openHalfBall (v : E) : Set E := {x | ‖x‖ < 1 ∧ 0 < inner ℝ v x}

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem norm_tangential_part_le (v x : E) (hv : ‖v‖ = 1) :
    ‖x - (inner ℝ v x) • v‖ ≤ ‖x‖ := by
  have he : ‖x - (inner ℝ v x) • v‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ v x) ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hv, mul_one,
      Real.norm_eq_abs, sq_abs, real_inner_comm x v]
    ring
  nlinarith [norm_nonneg x, norm_nonneg (x - (inner ℝ v x) • v), sq_nonneg (inner ℝ v x)]

theorem half_ball_hopf_lower
    (v : E) (hv : ‖v‖ = 1) (A : E → E →L[ℝ] E) {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {a R r l k lam L : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hRsmall : R ≤ 1 / 4)
    (hr : 0 < r) (hrsmall : r ≤ R / 4) (hl : 0 ≤ l) (hk : 0 ≤ k) (hlam : 0 < lam)
    (hscale : L * Module.finrank ℝ E ≤ 2 * a * lam * r ^ 2)
    (hpos : ∀ y ∈ closedHalfBall v, 0 ≤ u y)
    (hlo : ∀ y ∈ closedHalfBall v, ∀ w : E, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A y w))
    (hhi : ∀ y ∈ closedHalfBall v, ∀ w : E, inner ℝ w (A y w) ≤ L * ‖w‖ ^ 2)
    (hLu : ∀ y ∈ openHalfBall v, ellipticTrace A u y ≤ 2 * k * lam * Module.finrank ℝ E)
    (hinner : ∀ y ∈ Metric.closedBall (R • v) (2 * r), l ≤ u y) :
    ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      (l * a * R * Real.exp (-a * R ^ 2) - 2 * k * R) * inner ℝ v x ≤ u x := by
  intro x hxr ht
  let t := inner ℝ v x
  let w := x - t • v
  let z := w + R • v
  have ht_norm : t ≤ ‖x‖ := by
    simpa only [hv, one_mul] using real_inner_le_norm v x
  have ht_le : t ≤ r := ht_norm.trans hxr
  have hw : ‖w‖ ≤ r := (norm_tangential_part_le v x hv).trans hxr
  have hwv : inner ℝ v w = 0 := by simp [w, t, inner_sub_right, real_inner_smul_right,
    hv]
  have hzv : inner ℝ v z = R := by simp [z, inner_add_right, hwv, real_inner_smul_right,
    hv]
  have hznorm : ‖z‖ ≤ r + R := by
    exact (norm_add_le w (R • v)).trans (add_le_add hw (by simp [norm_smul, hv, abs_of_pos hR]))
  have hheight (y : E) : -‖y‖ ≤ inner ℝ v y := by
    have hh := abs_real_inner_le_norm v y
    rw [hv, one_mul, abs_le] at hh
    exact hh.1
  have hclosed (y : E) (hy : ‖y‖ ≤ R) : z + y ∈ closedHalfBall v := by
    constructor
    · have hn := (norm_add_le z y).trans (add_le_add hznorm hy)
      nlinarith
    · rw [inner_add_right, hzv]
      linarith [hheight y]
  have hopen (y : E) (hy : ‖y‖ < R) : z + y ∈ openHalfBall v := by
    constructor
    · have hn := (norm_add_le z y).trans (add_le_add hznorm hy.le)
      nlinarith
    · rw [inner_add_right, hzv]
      linarith [hheight y]
  have hutrans : ContDiff ℝ 2 (fun y => u (z + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have htrace (y : E) : ellipticTrace (fun q => A (z + q)) (fun q => u (z + q)) y =
      ellipticTrace A u (z + y) := by
    simpa only [rescalePoint, one_smul, one_pow, one_mul] using ellipticTrace_rescalePoint A hu z 1 y
  have hcomp := gaussian_hopf_annulus (fun y => A (z + y)) hutrans ha hr.le
    (by linarith : r < R) hl hk hlam hscale
    (fun y _ hy => hlo (z + y) (hclosed y hy))
    (fun y _ hy => hhi (z + y) (hclosed y hy))
    (fun y _ hy => by rw [htrace]; exact hLu (z + y) (hopen y hy))
    (fun y hy => hinner (z + y) (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : z + y - R • v = w + y := by dsimp [z]; module
      rw [he]
      exact (norm_add_le w y).trans (by linarith)))
    (fun y hy => hpos (z + y) (hclosed y hy.le))
  have hynorm : ‖(t - R) • v‖ = R - t := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith : t - R ≤ 0)]
    ring
  have hylo : r ≤ ‖(t - R) • v‖ := by rw [hynorm]; linarith
  have hyhi : ‖(t - R) • v‖ ≤ R := by rw [hynorm]; linarith
  have hux := hcomp ((t - R) • v) hylo hyhi
  have he : z + (t - R) • v = x := by dsimp [z, w]; module
  rw [he] at hux
  exact (hopfBarrier_normal_lower ha hl hk v hv ht (by linarith : t ≤ R)).trans hux

end OAI.Analysis.PDE.Elliptic
