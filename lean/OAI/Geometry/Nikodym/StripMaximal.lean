import OAI.Geometry.Nikodym.TruncatedPullback
import OAI.Geometry.Nikodym.DirectionChartIntegral
import OAI.MeasureTheory.Kakeya.Volume

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Module
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def stripDilation (V : ℝ) : ℝ := 2*(2+4*(1+2*V+1))
def stripMassConstant (V : ℝ) : ℝ := projectiveDistortion (3:ℝ)⁻¹ ((1+2*V+1)/(1/2))

def stripMaximal {d : ℕ} (δ V : ℝ) (f : Space (d+1) → ℂ) (x : Space d) : ℝ≥0∞ :=
  ⨆ v : Space d, ⨆ (_ : ‖v‖ ≤ V),
    (∫⁻ p in neighborhood δ (linePiece x v 1 2), ‖f (projectiveJoin d p)‖ₑ) /
      ENNReal.ofReal (δ^d)

theorem normalized_strip_mass_le_truncated {d : ℕ} {V δ : ℝ} (hV : 0 ≤ V)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) {x v : Space d} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ ≤ V)
    {f : Space (d+1) → ℂ} (hf : Measurable f) :
    let c := projectiveJoin d (v,0)+(3/4 : ℝ) • projectiveJoin d (x,1)
    (∫⁻ p in neighborhood δ (linePiece x v 1 2), ‖f (projectiveJoin d p)‖ₑ) ≤
      ENNReal.ofReal (stripMassConstant V)^(d+1) *
        volume (OAI.MeasureTheory.Kakeya.tube (stripDilation V*δ) (chartDirection d x) c) *
          OAI.MeasureTheory.Kakeya.kakeyaMaximal (stripDilation V*δ) (stripPullback d V f) (chartDirection d x) := by
  have hnorm : ‖projectiveJoin d (x,1)‖ ≤ 2 :=
    (projectiveJoin_norm_le d (x,1)).trans (by simp only [abs_one]; linarith)
  have h := normalized_strip_mass_le_kakeya (projectiveJoin d) x v (by norm_num : (0:ℝ)<2)
    (norm_projectiveJoin_le_two d) (by norm_num : (0:ℝ)≤1) hV hx hv hnorm hδ hδhalf
    (measurable_stripInput V hf)
  have hi : (∫⁻ p in neighborhood δ (linePiece x v 1 2),
      ‖stripInput d V f (projectiveJoin d p)‖ₑ) =
      ∫⁻ p in neighborhood δ (linePiece x v 1 2), ‖f (projectiveJoin d p)‖ₑ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_neighborhood _ _).measurableSet] with p hp
    rw [stripInput_on_neighborhood V f hx hv hδhalf hp]
  simp only [map_projectiveJoin_symm_volume,hi] at h
  simpa only [stripDilation,stripMassConstant,stripPullback,chartDirection,direction,
    Module.finrank_prod,Space,finrank_euclideanSpace,Fintype.card_fin,Module.finrank_self,
    mul_assoc] using! h

theorem divide_scaled_mass_bound {m k : ℝ≥0∞} {A U D δ : ℝ} (d : ℕ)
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hm : m ≤ ENNReal.ofReal A * ENNReal.ofReal (U*(D*δ)^d) * k) :
    m / ENNReal.ofReal (δ^d) ≤ ENNReal.ofReal (A*U*D^d)*k := by
  apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hδ _))) ENNReal.ofReal_ne_top).mpr
  apply hm.trans_eq
  simp only [mul_pow,ENNReal.ofReal_mul hU,ENNReal.ofReal_mul (pow_nonneg hD _),
    ENNReal.ofReal_mul hA,ENNReal.ofReal_mul (mul_nonneg hA hU)]
  simp only [mul_comm,mul_assoc]

theorem exists_stripMaximal_pointwise_bound (d : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → ∀ x : Space d, ‖x‖ ≤ 1 →
        stripMaximal δ V f x ≤ ENNReal.ofReal C *
          OAI.MeasureTheory.Kakeya.kakeyaMaximal (stripDilation V*δ) (stripPullback d V f) (chartDirection d x) := by
  obtain ⟨U,hU,hvol⟩ := OAI.MeasureTheory.Kakeya.exists_volume_tube_real_upper (n:=d+1) (by omega)
  have hD : 0 < stripDilation V := by dsimp [stripDilation]; positivity
  have hA : 0 < stripMassConstant V := by
    apply projectiveDistortion_pos (by norm_num)
    positivity
  refine ⟨(stripMassConstant V)^(d+1)*U*(stripDilation V)^d,by positivity,?_⟩
  intro δ hδ hδhalf hη f hf x hx
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hω : ‖chartDirection d x‖ = 1 := by
    apply norm_normalized
    intro hz
    have he := congrArg (fun y : Space (d+1) => y 0) hz
    simp at he
  let c := projectiveJoin d (v,0)+(3/4 : ℝ) • projectiveJoin d (x,1)
  have hmass := normalized_strip_mass_le_truncated hV hδ hδhalf hx hv hf
  have htvol : volume (OAI.MeasureTheory.Kakeya.tube (stripDilation V*δ) (chartDirection d x) c) ≤
      ENNReal.ofReal (U*(stripDilation V*δ)^d) := by
    rw [← ENNReal.ofReal_toReal (OAI.MeasureTheory.Kakeya.volume_tube_lt_top _ _ _).ne]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.add_sub_cancel] using! hvol (stripDilation V*δ) (chartDirection d x) c
      (mul_pos hD hδ) hη hω
  apply divide_scaled_mass_bound d (pow_pos hA _).le hU.le hD.le hδ
  rw [ENNReal.ofReal_pow hA.le]
  exact hmass.trans (mul_le_mul' (mul_le_mul' le_rfl htvol) le_rfl)

end OAI.Geometry.Nikodym
