import OAI.Analysis.Normed.Function.Sobolev.Reflection.Map

open Set _root_.MeasureTheory Filter
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d : ℕ}

theorem normalScale_quasiMeasurePreserving (k : Fin d) {a : ℝ} (ha : a≠0) :
    Measure.QuasiMeasurePreserving (normalScale k a) volume volume := by
  refine ⟨(normalScale k a).continuous.measurable,?_⟩
  rw [map_volume_normalScale k ha]
  intro s hs
  simp [hs]

theorem memLp_normalScale (k : Fin d) {a : ℝ} (ha : a≠0)
    {p : ENNReal} {f : (Fin d→ℝ)→ℝ} (hf : MemLp f p volume) :
    MemLp (fun x ↦ f (normalScale k a x)) p volume := by
  have hm : MemLp f p (Measure.map (normalScale k a) volume) := by
    rw [map_volume_normalScale k ha]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_of_map (normalScale k a).continuous.measurable.aemeasurable

theorem integrable_normalScale (k : Fin d) {a : ℝ} (ha : a≠0)
    {f : (Fin d→ℝ)→ℝ} (hf : Integrable f) :
    Integrable (fun x ↦ f (normalScale k a x)) := by
  exact (memLp_one_iff_integrable).mp (memLp_normalScale k ha (memLp_one_iff_integrable.mpr hf))

theorem integral_normalScale (k : Fin d) {a : ℝ} (ha : a≠0) (f : (Fin d→ℝ)→ℝ) :
    (∫x,f (normalScale k a x))=|a⁻¹| *(∫x,f x) := by
  let e := (normalScaleEquiv k a ha).toHomeomorph.toMeasurableEquiv
  have he := integral_map_equiv (μ := volume) e f
  change (∫x,f x ∂Measure.map (normalScale k a) volume)=∫x,f (normalScale k a x) at he
  rw [map_volume_normalScale k ha,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at he
  exact he.symm

theorem setIntegral_normalScale_negative
    (k : Fin d) {a : ℝ} (ha : a<0) (f φ : (Fin d→ℝ)→ℝ) :
    (∫x in {x|x k<0},f (normalScale k a x)*φ x)=
      |a⁻¹| *(∫y in {y|0<y k},f y*φ (normalScale k a⁻¹ y)) := by
  have hneg : MeasurableSet {x : Fin d→ℝ|x k<0} := measurableSet_lt (measurable_pi_apply k) measurable_const
  have hpos : MeasurableSet {x : Fin d→ℝ|0<x k} := measurableSet_lt measurable_const (measurable_pi_apply k)
  let F : (Fin d→ℝ)→ℝ := {y : Fin d→ℝ|0<y k}.indicator (fun y ↦ f y*φ (normalScale k a⁻¹ y))
  have hF x : F (normalScale k a x)=
      {y : Fin d→ℝ|y k<0}.indicator (fun y ↦ f (normalScale k a y)*φ y) x := by
    have hiff : 0<normalScale k a x k ↔ x k<0 := by
      rw [normalScale_apply_same]
      constructor
      · intro h
        by_contra hn
        exact (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg ha.le (le_of_not_gt hn))) h
      · exact fun hx ↦ mul_pos_of_neg_of_neg ha hx
    by_cases hx : x k<0
    · simp only [F,indicator,Set.mem_ofPred_eq,hx,hiff.mpr hx,ite_true,
        normalScale_comp,inv_mul_cancel₀ ha.ne,normalScale_one]
    · have hn : ¬0<normalScale k a x k := fun h ↦ hx (hiff.mp h)
      simp only [F,indicator,Set.mem_ofPred_eq,hn,hx,ite_false]
  have h := integral_normalScale k ha.ne F
  simp_rw [hF] at h
  rw [integral_indicator hneg] at h
  simpa only [F,integral_indicator hpos] using h

end OAI.Analysis.Normed.Function.Sobolev
