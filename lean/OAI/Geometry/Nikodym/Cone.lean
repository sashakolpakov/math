import OAI.Geometry.Nikodym.ProjectiveIntegral

noncomputable section
open Set
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cone (p : E × ℝ) : E × ℝ := (p.2 • p.1,p.2)
def coneInverse (p : E × ℝ) : E × ℝ := (p.2⁻¹ • p.1,p.2)

theorem coneInverse_cone {p : E × ℝ} (hp : p.2 ≠ 0) :
    coneInverse (cone p) = p := by
  simp only [cone,coneInverse,smul_smul,inv_mul_cancel₀ hp,one_smul]

theorem dist_coneInverse_le {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (p q : E × ℝ) (hp : a ≤ |p.2|) (hq : a ≤ |q.2|) (hy : ‖q.1‖ ≤ R) :
    dist (coneInverse p) (coneInverse q) ≤
      (projectiveDistortion a R+1)*dist p q := by
  have hP := dist_projective_le ha hR p q hp hq hy
  change dist (projective p) (projective q) ≤ projectiveDistortion a R * dist p q at hP
  have hpos := (projectiveDistortion_pos ha hR).le
  rw [dist_eq_norm,Prod.norm_def]
  apply max_le
  · have hfst : ‖(coneInverse p-coneInverse q).1‖ ≤
        dist (projective p) (projective q) := by
      rw [dist_eq_norm,Prod.norm_def]
      exact le_max_left _ _
    exact (hfst.trans hP).trans (by nlinarith [dist_nonneg (x:=p) (y:=q)])
  · have hsnd : ‖(coneInverse p-coneInverse q).2‖ ≤ dist p q := by
      rw [dist_eq_norm,Prod.norm_def]
      exact le_max_right _ _
    exact hsnd.trans (by nlinarith [dist_nonneg (x:=p) (y:=q)])

theorem lipschitzOn_coneInverse {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    LipschitzOnWith ⟨projectiveDistortion a R+1,by linarith [projectiveDistortion_pos ha hR]⟩
      (coneInverse : E × ℝ → E × ℝ) {p | a ≤ |p.2| ∧ ‖p.1‖ ≤ R} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  exact dist_coneInverse_le ha hR p q hp.1 hq.1 hq.2

variable [MeasurableSpace E] [BorelSpace E]

theorem measurable_cone : Measurable (cone : E × ℝ → E × ℝ) := by
  unfold cone
  fun_prop

theorem measurable_coneInverse : Measurable (coneInverse : E × ℝ → E × ℝ) := by
  unfold coneInverse
  fun_prop

end OAI.Geometry.Nikodym
