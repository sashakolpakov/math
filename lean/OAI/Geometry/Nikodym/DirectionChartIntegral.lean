import OAI.Geometry.Nikodym.CoordinateMeasure
import OAI.Geometry.Nikodym.RadialDirectionIntegral
import OAI.Geometry.Nikodym.Cone

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def chartDirection (d : ℕ) (x : Space d) : Space (d+1) :=
  direction (projectiveJoin d (x,1))

theorem measurable_chartDirection (d : ℕ) : Measurable (chartDirection d) :=
  measurable_direction.comp ((projectiveJoin d).continuous.measurable.comp
    (measurable_id.prodMk measurable_const))

theorem cone_join_direction (d : ℕ) {p : Space d × ℝ} (hp : 0 < p.2) :
    direction (projectiveJoin d (cone p)) = chartDirection d p.1 := by
  have he : cone p = p.2 • (p.1,(1:ℝ)) := by ext <;> simp [cone]
  rw [he,map_smul,direction_pos_smul _ hp]
  rfl

theorem norm_cone_join_le (d : ℕ) {R : ℝ} (_ : 0 ≤ R)
    {p : Space d × ℝ} (hp : p ∈ closedBall 0 R ×ˢ Icc (1:ℝ) 2) :
    ‖projectiveJoin d (cone p)‖ ≤ 2*(R+1) := by
  have hx : ‖p.1‖ ≤ R := mem_closedBall_zero_iff.mp hp.1
  have ht0 : 0 ≤ p.2 := (by norm_num : (0:ℝ) ≤ 1).trans hp.2.1
  calc
    _ ≤ ‖(cone p).1‖+|(cone p).2| := projectiveJoin_norm_le d _
    _ = p.2*‖p.1‖+p.2 := by simp only [cone,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    _ ≤ 2*R+2 := add_le_add (mul_le_mul hp.2.2 hx (norm_nonneg _) (by norm_num)) hp.2.2
    _ = _ := by ring

/-- The bounded affine chart of directions is quantitatively absolutely
continuous with respect to the actual sphere measure. This is proved by
coning, Haar measure distortion and polar integration. -/
theorem lintegral_chartDirection_le {d : ℕ} {R : ℝ} (hR : 0 < R)
    {H : Space (d+1) → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x in closedBall 0 R, H (chartDirection d x)) ≤
      (ENNReal.ofReal (projectiveDistortion 1 (2*R)+1) ^ (d+1)) *
        ENNReal.ofReal ((2*(R+1))*(2*(R+1))^d) *
          ∫⁻ ω, H ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure (d+1) := by
  let : (volume : Measure (Space d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let s : Set (Space d × ℝ) := closedBall 0 R ×ˢ Icc 1 2
  let B : ℝ := 2*(R+1)
  let F : Space (d+1) → ℝ≥0∞ := (closedBall 0 B).indicator (H ∘ direction)
  let G : Space d × ℝ → ℝ≥0∞ := F ∘ projectiveJoin d
  have hs : MeasurableSet s := isClosed_closedBall.measurableSet.prod measurableSet_Icc
  have hF : Measurable F := (hH.comp measurable_direction).indicator isClosed_closedBall.measurableSet
  have hG : Measurable G := hF.comp (projectiveJoin d).continuous.measurable
  have hmap : MapsTo (cone : Space d × ℝ → Space d × ℝ) s
      {q | 1 ≤ |q.2| ∧ ‖q.1‖ ≤ 2*R} := by
    intro p hp
    have hx : ‖p.1‖ ≤ R := mem_closedBall_zero_iff.mp hp.1
    have ht0 : 0 ≤ p.2 := (by norm_num : (0:ℝ) ≤ 1).trans hp.2.1
    change 1 ≤ |p.2| ∧ ‖p.2 • p.1‖ ≤ 2*R
    rw [abs_of_nonneg ht0,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact ⟨hp.2.1,mul_le_mul hp.2.2 hx (norm_nonneg _) (by norm_num)⟩
  have hinv : ∀ p ∈ s, coneInverse (cone p) = p := by
    intro p hp
    exact coneInverse_cone (ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le hp.2.1))
  have htransport := lintegral_comp_restrict_le_of_lipschitz_inverse
    (volume : Measure (Space d × ℝ)) measurable_cone
    (lipschitzOn_coneInverse (by norm_num : (0:ℝ)<1) (by positivity : 0 ≤ 2*R))
    hmap hinv hG
  have hleft : (∫⁻ p in s, G (cone p)) = ∫⁻ x in closedBall 0 R, H (chartDirection d x) := by
    calc
      _ = ∫⁻ p in s, H (chartDirection d p.1) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hs] with p hp
        have hp0 : 0 < p.2 := (by norm_num : (0:ℝ)<1).trans_le hp.2.1
        have hb : projectiveJoin d (cone p) ∈ closedBall 0 B :=
          mem_closedBall_zero_iff.mpr (norm_cone_join_le d hR.le hp)
        simp only [G,F,Function.comp_apply,indicator_of_mem hb,cone_join_direction d hp0]
      _ = _ := by
        rw [Measure.volume_eq_prod,setLIntegral_prod]
        · simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
          norm_num
        · exact ((hH.comp (measurable_chartDirection d)).comp measurable_fst).aemeasurable
  have hright : (∫⁻ p, G p) = ∫⁻ y in closedBall 0 B, H (direction y) := by
    rw [← lintegral_indicator isClosed_closedBall.measurableSet]
    have hm := (measurePreserving_projectiveJoin d).map_eq
    calc
      _ = ∫⁻ y, F y ∂Measure.map (projectiveJoin d) volume :=
        (lintegral_map hF (projectiveJoin d).continuous.measurable).symm
      _ = _ := by rw [hm]; rfl
  rw [hleft,hright] at htransport
  have hpole := lintegral_radial_direction_ball (n:=d+1) (by omega)
    (R:=B) (by dsimp [B]; positivity) hH
  have hk : 0 ≤ projectiveDistortion 1 (2*R)+1 := by
    have hh := projectiveDistortion_pos (by norm_num : (0:ℝ)<1) (by positivity : 0 ≤ 2*R)
    linarith
  have htransport' : (∫⁻ x in closedBall 0 R, H (chartDirection d x)) ≤
      ENNReal.ofReal (projectiveDistortion 1 (2*R)+1)^finrank ℝ (Space d × ℝ) *
        ∫⁻ y in closedBall 0 B, H (direction y) := by
    simpa only [ENNReal.ofReal_eq_coe_nnreal hk] using! htransport
  have hd : finrank ℝ (Space d × ℝ) = d+1 := by
    simp [Space,Module.finrank_prod]
  rw [hd] at htransport'
  exact htransport'.trans (by
    rw [mul_assoc]
    apply mul_le_mul' le_rfl
    simpa only [B,Nat.add_sub_cancel] using hpole)

end OAI.Geometry.Nikodym
