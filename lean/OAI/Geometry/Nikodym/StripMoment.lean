import OAI.Geometry.Nikodym.StripLp

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem stripMaximal_local_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (stripMaximal δ V f) (d+1 : ℕ) (volume.restrict (closedBall 0 1)) ≤
          ENNReal.ofReal (C*δ^(-ε)) * eLpNorm (stripInput d V f) (d+1 : ℕ) volume := by
  obtain ⟨C,hC,h⟩ := stripMaximal_local_bound_ennreal hK hd hV hε
  refine ⟨C.toReal+1,by positivity,?_⟩
  intro δ hδ hh hD f hf hfp
  apply (h δ hδ hh hD f hf hfp).trans
  apply mul_le_mul' _ le_rfl
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal+1)]
  apply mul_le_mul' _ le_rfl
  calc
    C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
    _ ≤ ENNReal.ofReal (C.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)

theorem eLpNorm_nat_pow_eq_lintegral {X F : Type*} [MeasurableSpace X]
    [TopologicalSpace F] [ESeminormedAddMonoid F] {μ : Measure X}
    {f : X → F} {n : ℕ} (hn : 0 < n) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f n μ ^ n = ∫⁻ x, ‖f x‖ₑ^n ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p:=(n:NNReal))
    (by exact_mod_cast hn.ne') hf
  simpa only [ENNReal.coe_natCast,NNReal.coe_natCast,ENNReal.rpow_natCast] using h

theorem stripMaximal_local_moment_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/2 → stripDilation V*δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        (∫⁻ x in closedBall 0 1, stripMaximal δ V f x ^ (d+1)) ≤
          ENNReal.ofReal (C*δ^(-ε))^(d+1) *
            ∫⁻ y in (projectiveJoin d).symm ⁻¹' stripBox d V, ‖f y‖ₑ^(d+1) := by
  obtain ⟨C,hC,h⟩ := stripMaximal_local_bound hK hd hV hε
  refine ⟨C,hC,?_⟩
  intro δ hδ hh hD f hf hfp
  have hpow := pow_le_pow_left' (h δ hδ hh hD f hf hfp) (d+1)
  rw [mul_pow,eLpNorm_nat_pow_eq_lintegral (by omega)
    (measurable_stripMaximal δ V hf).aestronglyMeasurable] at hpow
  have hs := (measurableSet_stripBox d V).preimage (projectiveJoin d).symm.continuous.measurable
  rw [show stripInput d V f = ((projectiveJoin d).symm ⁻¹' stripBox d V).indicator f from rfl,
    eLpNorm_indicator_eq_eLpNorm_restrict hs,
    eLpNorm_nat_pow_eq_lintegral (by omega) hf.aestronglyMeasurable] at hpow
  simpa using hpow

end OAI.Geometry.Nikodym
