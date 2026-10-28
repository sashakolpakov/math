import OAI.Geometry.Nikodym.FullStrip
import OAI.Geometry.Nikodym.StripMoment
import OAI.Geometry.Nikodym.Averaging

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem fullStrip_moment_from_local {d : ℕ} {δ V : ℝ} {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hlocal : ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
      (∫⁻ x in closedBall 0 1, stripMaximal δ V f x^(d+1)) ≤
        A * ∫⁻ y in (projectiveJoin d).symm ⁻¹' stripBox d V, ‖f y‖ₑ^(d+1))
    {f : Space (d+1) → ℂ} (hf : Measurable f) (hfp : MemLp f (d+1 : ℕ) volume) :
    volume (closedBall (0:Space d) 1) * (∫⁻ z, fullStrip δ V f z^(d+1)) ≤
      A * (volume ((projectiveJoin d).symm ⁻¹' stripBox d V) * (∫⁻ y, ‖f y‖ₑ^(d+1))) := by
  have hshift (z : Space (d+1)) : MemLp (fun y => f (z+y)) (d+1 : ℕ) volume := by
    have he := eLpNorm_comp_measurePreserving (p:=(d+1 : ℕ)) hf.aestronglyMeasurable
      (measurePreserving_add_left (volume : Measure (Space (d+1))) z)
    change eLpNorm (fun y => f (z+y)) (d+1 : ℕ) volume < ⊤
    simp only [Function.comp_def] at he
    rw [he]
    exact hfp
  have hpoint (z : Space (d+1)) :
      (∫⁻ x in closedBall (0:Space d) 1, fullStrip δ V f (z+projectiveJoin d (x,0))^(d+1)) ≤
        A * ∫⁻ y in (projectiveJoin d).symm ⁻¹' stripBox d V, ‖f (z+y)‖ₑ^(d+1) := by
    simpa only [fullStrip_eq_local δ V hf] using
      hlocal (fun y => f (z+y)) (hf.comp (measurable_const.add measurable_id)) (hshift z)
  have hint := lintegral_mono (μ:=(volume : Measure (Space (d+1)))) hpoint
  rw [lintegral_const_mul' A _ hA] at hint
  rw [lintegral_translation_average_map (volume : Measure (Space (d+1))) volume
    (show Measurable (fun x : Space d => projectiveJoin d (x,0)) by fun_prop)
    ((measurable_fullStrip δ V hf).pow_const (d+1)),
    lintegral_translation_average (volume : Measure (Space (d+1))) (hf.enorm.pow_const (d+1))] at hint
  exact hint

theorem stripInput_volume_lt_top (d : ℕ) (V : ℝ) :
    volume ((projectiveJoin d).symm ⁻¹' stripBox d V) < ⊤ := by
  apply (measure_mono (t:=closedBall 0 (5+2*V)) ?_).trans_lt
    (isCompact_closedBall (0:Space (d+1)) (5+2*V)).measure_lt_top
  intro y hy
  change (1/2:ℝ) ≤ |((projectiveJoin d).symm y).2| ∧
    |((projectiveJoin d).symm y).2| ≤ 3 ∧ ‖((projectiveJoin d).symm y).1‖ ≤ 2+2*V at hy
  rw [mem_closedBall,dist_zero_right]
  have hn := projectiveJoin_norm_le d ((projectiveJoin d).symm y)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hn
  linarith [hy.2.1,hy.2.2]

theorem fullStrip_moment_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        (∫⁻ z, fullStrip δ V f z^(d+1)) ≤
          C * ENNReal.ofReal (δ^(-ε))^(d+1) * (∫⁻ y, ‖f y‖ₑ^(d+1)) := by
  obtain ⟨C,hC,hlocal⟩ := stripMaximal_local_moment_bound hK hd hV hε
  let B := volume (closedBall (0:Space d) 1)
  let R := volume ((projectiveJoin d).symm ⁻¹' stripBox d V)
  have hB : B ≠ 0 := by
    apply ne_of_gt
    exact measure_closedBall_pos volume _ (by norm_num)
  have hBt : B ≠ ⊤ := (isCompact_closedBall (0:Space d) 1).measure_lt_top.ne
  have hR : R < ⊤ := stripInput_volume_lt_top d V
  refine ⟨B⁻¹ * ENNReal.ofReal C^(d+1) * R,by finiteness,?_⟩
  intro δ hδ hh hD f hf hfp
  have h := fullStrip_moment_from_local (by finiteness)
    (hlocal δ hδ hh hD) hf hfp
  have hm := mul_le_mul' (le_refl B⁻¹) h
  change B⁻¹ * (B * _) ≤ _ at hm
  rw [← mul_assoc,ENNReal.inv_mul_cancel hB hBt,one_mul] at hm
  apply hm.trans_eq
  rw [ENNReal.ofReal_mul hC.le,mul_pow]
  dsimp only [R]
  ac_rfl

end OAI.Geometry.Nikodym
