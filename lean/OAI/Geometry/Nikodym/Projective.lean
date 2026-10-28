import Mathlib

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The projective involution exchanging a passing point on the hyperplane
`t = 0` with a line direction. It is used only off that hyperplane. -/
def projective (p : E × ℝ) : E × ℝ := (p.2⁻¹ • p.1,p.2⁻¹)

theorem projective_involutive {p : E × ℝ} (hp : p.2 ≠ 0) :
    projective (projective p) = p := by
  simp only [projective,inv_inv,smul_smul,mul_inv_cancel₀ hp,one_smul]

theorem projective_line (x v : E) {t : ℝ} (ht : t ≠ 0) :
    projective (x + t • v,t) = (v,0) + t⁻¹ • (x,1) := by
  ext <;> simp only [projective,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_add,smul_smul,inv_mul_cancel₀ ht,one_smul,smul_eq_mul,mul_one,zero_add]
  exact add_comm _ _

theorem projective_injectiveOn :
    InjOn (projective : E × ℝ → E × ℝ) {p | p.2 ≠ 0} := by
  intro p hp q hq he
  have h := congrArg projective he
  simpa only [projective_involutive hp,projective_involutive hq] using h

theorem projective_mapsTo :
    MapsTo (projective : E × ℝ → E × ℝ) {p | p.2 ≠ 0} {p | p.2 ≠ 0} :=
  fun _ h => inv_ne_zero h

theorem contDiffAt_projective {p : E × ℝ} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (projective : E × ℝ → E × ℝ) p := by
  exact ((contDiffAt_snd.inv hp).smul contDiffAt_fst).prodMk (contDiffAt_snd.inv hp)

theorem contDiffOn_projective :
    ContDiffOn ℝ ∞ (projective : E × ℝ → E × ℝ) {p | p.2 ≠ 0} :=
  fun _ hp => (contDiffAt_projective hp).contDiffWithinAt

theorem projective_sub (p q : E × ℝ) :
    projective p - projective q =
      (p.2⁻¹ • (p.1-q.1) + (p.2⁻¹-q.2⁻¹) • q.1,p.2⁻¹-q.2⁻¹) := by
  ext <;> simp only [projective,Prod.fst_sub,Prod.snd_sub,smul_sub,sub_smul]
  abel

/-- Reciprocal distortion on a fixed annular strip. -/
theorem abs_inv_sub_inv_le {a t u : ℝ} (ha : 0 < a)
    (ht : a ≤ |t|) (hu : a ≤ |u|) :
    |t⁻¹-u⁻¹| ≤ |t-u| / a ^ 2 := by
  have ht0 : t ≠ 0 := abs_pos.mp (ha.trans_le ht)
  have hu0 : u ≠ 0 := abs_pos.mp (ha.trans_le hu)
  rw [inv_sub_inv ht0 hu0,abs_div,abs_mul,abs_sub_comm]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ha)
  nlinarith [mul_le_mul ht hu ha.le (abs_nonneg t)]

/-- The projective map has uniformly bounded distortion on bounded pieces
away from its pole, the precise fact required for tube neighborhoods. -/
theorem dist_projective_le {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (p q : E × ℝ) (hp : a ≤ |p.2|) (hq : a ≤ |q.2|) (hy : ‖q.1‖ ≤ R) :
    dist (projective p) (projective q) ≤
      (a⁻¹ + (R+1) / a^2) * dist p q := by
  have hd1 : ‖p.1-q.1‖ ≤ dist p q := by
    rw [dist_eq_norm,Prod.norm_def]
    exact le_max_left _ _
  have hd2 : |p.2-q.2| ≤ dist p q := by
    rw [dist_eq_norm,Prod.norm_def]
    exact le_max_right _ _
  have hi : |p.2⁻¹| ≤ a⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ ha hp
  have hs := abs_inv_sub_inv_le ha hp hq
  have hs' : |p.2⁻¹-q.2⁻¹| ≤ dist p q / a^2 :=
    hs.trans (div_le_div_of_nonneg_right hd2 (sq_nonneg a))
  rw [dist_eq_norm,projective_sub,Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖p.2⁻¹ • (p.1-q.1)‖ + ‖(p.2⁻¹-q.2⁻¹) • q.1‖ := norm_add_le _ _
      _ = |p.2⁻¹| * ‖p.1-q.1‖ + |p.2⁻¹-q.2⁻¹| * ‖q.1‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ a⁻¹*dist p q + (dist p q/a^2)*R :=
        add_le_add (mul_le_mul hi hd1 (norm_nonneg _) (inv_nonneg.mpr ha.le))
          (mul_le_mul hs' hy (norm_nonneg _) (by positivity))
      _ ≤ _ := by
        have : 0 ≤ dist p q / a^2 := by positivity
        rw [show (a⁻¹ + (R+1)/a^2)*dist p q =
          a⁻¹*dist p q + (dist p q/a^2)*R + dist p q/a^2 by ring]
        nlinarith
  · rw [Real.norm_eq_abs]
    apply hs'.trans
    have hnon : 0 ≤ a⁻¹*dist p q := by positivity
    have hmul : 0 ≤ R*(dist p q/a^2) := by positivity
    rw [show (a⁻¹ + (R+1)/a^2)*dist p q =
      a⁻¹*dist p q + R*(dist p q/a^2) + dist p q/a^2 by ring]
    nlinarith

end OAI.Geometry.Nikodym
